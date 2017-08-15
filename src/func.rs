use rush_rt::vars::{LocalVars, Scoped};
use rush_rt::val::Val;
use rush_parser::ast::{ExprS};
use rush_pat::pat::{Pat};
use rush_rt::pat::{ValMatcher};
use rush_pat::subsume::{Subsumes, Subsumption};
use interp::Interp;
use std::collections::HashMap;
use std::borrow::Cow;
use std::fmt;

type BuiltinFn = fn(&Interp, &mut LocalVars) -> Val;

pub enum FuncBody {
    BuiltIn(BuiltinFn),
    User(Vec<ExprS>),
}

impl Clone for FuncBody {
    fn clone(&self) -> Self {
        match *self {
            FuncBody::BuiltIn(f) => FuncBody::BuiltIn(f),
            FuncBody::User(ref v) => FuncBody::User(v.clone()),
        }
    }
}

impl PartialEq for FuncBody {
    fn eq(&self, o: &FuncBody) -> bool {
        use self::FuncBody::*;

        match (self, o) {
            (&User(..), &BuiltIn(..)) | (&BuiltIn(..), &User(..)) => false,
            (&User(ref sv), &User(ref ov)) => sv == ov,
            (&BuiltIn(ref sf), &BuiltIn(ref of)) => sf as *const _ == of as *const _,
        }
    }
}

impl fmt::Debug for FuncBody {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use self::FuncBody::*;

        match *self {
            BuiltIn(_) => write!(f, "<built-in>"),
            User(ref v) => write!(f, "{{{:?}}}", v),
        }
    }
}

#[derive(Clone, PartialEq)]
pub struct Func {
    pub args: Pat,
    pub body: FuncBody,
}

impl fmt::Debug for Func {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "|{:?}| {:?}", self.args, self.body)
    }
}

impl Func {
    pub fn built_in(args: Pat, f: BuiltinFn) -> Func {
        use self::FuncBody::*;

        Func{args: args, body: BuiltIn(f)}
    }

    pub fn user(args: Pat, f: Vec<ExprS>) -> Func {
        use self::FuncBody::*;

        Func{args: args, body: User(f)}
    }

    /*
    pub fn into_lambda(f: Func) -> Func {
        lazy_static! { static ref LAMBDA_COUNT: usize = 0; }
        let name = Pat::Str(format!("@lambda{}@", *LAMBDA_COUNT));
        println!("into_lambda: {:?}", f);
        let args = match f.args {
            Some(mut args @ Pat::Tup(..)) => {
                if let Pat::Tup(ref mut v) = args {
                    v.insert(0, name);
                } else { unreachable!() }
                args
            },
            Some(args) => Pat::Tup(vec![name, args]),
            None => Pat::Tup(vec![name]),
        };
        Func{args: Some(args), body: f.body}
    }
    */
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum Control {
    Done,
    Return,
    Break,
    Continue,
    Exit,
}

impl Control {
    pub fn breaks_loops(self) -> bool {
        use self::Control::*;
        match self {
            Return | Break | Exit => true,
            Done | Continue => false,
        }
    }

    pub fn stops_exec(self) -> bool {
        use self::Control::*;
        match self {
            Return | Continue | Break | Exit => true,
            Done => false,
        }
    }

    pub fn clear_breaks(&mut self) {
        use self::Control::*;
        if *self != Return && *self != Exit {
            *self = Done
        }
    }
}

/*
impl StmtResult {
    pub fn take_val(self) -> Option<Val> {
        use self::StmtResult::*;

        match self {
            Done(v) | Return(v) | Break(v) | Continue(v) => Some(v),
        }
    }

    pub fn val(&self) -> Option<&Val> {
        use self::StmtResult::*;

        match *self {
            Done(ref v) | Return(ref v) | Break(ref v) | Continue(ref v) => Some(v),
        }
    }
}*/

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
struct ArgSig {
    pub depth: usize,
    pub name: String,
}

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
struct FuncKey {
    pub arg0: ArgSig,
    pub arg1: Option<ArgSig>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct FuncMap {
    map: HashMap<FuncKey, Vec<Func>>,
}

impl ArgSig {
    pub fn from_pat(p: &Pat) -> Option<ArgSig> {
        use self::Pat::*;
        let mut depth = 0;
        let mut cur = p;
        loop {
            match cur {
                &Str(ref s) => return Some(ArgSig{depth: depth, name: s.to_string()}),
                &Tup(ref v) => {
                    if v.len() == 0 { return None }
                    depth += 1;
                    cur = &v[0];
                }
                &Bind(_, ref p) => cur = p,
                _ => return None
            }
        }
    }

    pub fn from_val(v: &Val, mut embed: usize, mut depth: usize) -> Option<ArgSig> {
        use self::Val::*;
        let mut cur = v;
        loop {
            match cur {
                &Str(ref s) => return Some(ArgSig{depth: depth, name: s.to_string()}),
                &Embed(ref e) => {
                    embed += 1;
                    cur = &*e;
                },
                &Ref(ref s) => {
                    return Self::from_val(&*s.get_ref(), embed, depth);
                },
                &Tup(ref v) => {
                    if v.len() == 0 { return None }
                    if embed == 0 { depth += 1 } else { embed -= 1 }
                    cur = &v[0];
                },
                _ => return None
            }
        }
    }
}

impl FuncKey {
    pub fn from_pat(p: &Pat) -> FuncKey {
        use self::Pat::*;

        if let &Tup(ref v) = p {
            if v.len() == 0 { panic!("Function pattern tuple cannot be empty"); }
            if let Some(sig0) = ArgSig::from_pat(&v[0]) {
                let sig1 = if v.len() > 1 { ArgSig::from_pat(&v[1]) } else { None };
                return FuncKey{ arg0: sig0, arg1: sig1 };
            } else {
                panic!("Function pattern's left most non-tuple must be a scalar string");
            }
        } else {
            panic!("Function pattern must be a tuple");
        }
    }

    pub fn from_val(v: &Val) -> FuncKey {
        use self::Val::*;

        match v {
            &Tup(ref v) => {
                if v.len() == 0 { panic!("Function call tuple cannot be empty"); }
                if let Some(sig0) = ArgSig::from_val(&v[0], 0, 0) {
                    let sig1 = if v.len() > 1 { ArgSig::from_val(&v[1], 0, 0) } else { None };
                    return FuncKey{ arg0: sig0, arg1: sig1 };
                } else {
                    panic!("Function call's left most non-tuple must be a scalar string");
                }
            },
            &Str(ref s) => return FuncKey{ arg0: ArgSig{depth: 0, name: s.to_string()}, arg1: None },
            &Ref(ref r) => Self::from_val(&*r.get_ref()),
            &Embed(ref e) => Self::from_val(&*e),
            _ => panic!("Function call value must be scalar string or tuple"),
        }
    }
}

impl FuncMap {
    pub fn new() -> FuncMap {
        FuncMap{map: HashMap::new()}
    }

    fn try_lookup(&self, v: &Val, key: &FuncKey) -> Option<&Func> {
        //println!("Looking up key {:?} for val {:?}", key, v);
        if let Some(list) = self.map.get(&key) {
            //println!("  Overloads: {:?}", list);
            for ref func in list {
                if func.args.subsumes(v).same_or_contains() {
                    return Some(func)
                }
            }
        }
        return None;
    }

    fn lookup_impl(&self, mut v: Val) -> (Val, Option<&Func>) {
        //println!("Looking up val {:?}", &v);
        let mut key = FuncKey::from_val(&v);
        if let Some(f) = self.try_lookup(&v, &key) {
            return (v, Some(f))
        }
        let mut tmp = None;
        ::std::mem::swap(&mut tmp, &mut key.arg1);
        if let Some(f) = self.try_lookup(&v, &key) {
            return (v, Some(f))
        }
        ::std::mem::swap(&mut tmp, &mut key.arg1);
        if key.arg0.depth >= 1 {
            v.eval();
            while key.arg0.depth > 0 {
                if let Some(v) = v.get_tup_mut() {
                    //println!("v: {:?}", v);
                    let mut tmp = Val::void();
                    ::std::mem::swap(&mut tmp, &mut v[0]);
                    v.splice(0..1, tmp.take_tup().unwrap());
                } else {
                    break;
                }
                key.arg0.depth -= 1;
                if let Some(f) = self.try_lookup(&v, &key) {
                    return (v, Some(f))
                }
                let mut tmp = None;
                ::std::mem::swap(&mut tmp, &mut key.arg1);
                if let Some(f) = self.try_lookup(&v, &key) {
                    return (v, Some(f))
                }
                ::std::mem::swap(&mut tmp, &mut key.arg1);
            }
        }
        return (v, None);
    }

    pub fn lookup(&self, val: Val) -> Result<(LocalVars, FuncBody), Val> {
        if let Val::Embed(v) = val {
            return self.lookup(*v);
        }
        let (val, func) = self.lookup_impl(val);
        if let Some(func) = func {
            let mut locals = LocalVars::new();
            locals.enter_scope();
            func.args.do_match_unchecked(Cow::from(val), &mut locals);
            Ok((locals, func.body.clone()))
        } else {
            Err(val)
        }
    }

    pub fn reg(&mut self, b: Func) -> bool {
        use self::Subsumption::*;

        let key;
        //println!("Registering fn {:?}", b);
        key = FuncKey::from_pat(&b.args);
        if let Some(ref mut v) = self.map.get_mut(&key) {
            let mut pos = None;
            for (i, ref o) in v.iter().enumerate() {
                match b.args.subsumes(&o.args) {
                    ContainedBy => {
                        pos = Some(i);
                        break;
                    },
                    Overlaps | Same => {
                        return false;
                    },
                    _ => {},
                }
            }
            //println!("Registering fn overload {:?}", pat);
            if let Some(pos) = pos {
                v.insert(pos, b);
            } else {
                v.push(b);
            }
            return true;
            //println!("Registering fn {:?}", pat);
            //println!("  Overload set: {:?}", v);
        }
        //println!("Adding for new key {:?}", key);
        let e = self.map.entry(key);
        e.or_insert(vec![b]);
        return true;
    }
}
