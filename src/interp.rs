use rush_parser::ast::{ExprS, Expr, SetOp, ImportScope, SubsMode, Span};
use rush_pat::pat::Pat;
use rush_pat::range::Range;
use rush_rt::vars::{VarRef, LocalVars, Resolver, Binder, Scoped};
use rush_rt::val::{Val, InternalIterable};
use rush_rt::error::{RuntimeError};
use rush_rt::pat::{ValMatcher};
use rush_rt::range::{RangeExt};
use rush_pat::subsume::{Subsumes, Subsumption};
use std::collections::{HashMap, BTreeMap};
use std::borrow::Cow;
use func::{Control, Func, FuncBody, FuncMap};
use std::cell::RefCell;
use std::rc::Rc;

type VarMap = HashMap<String, VarRef>;

type JobMap = BTreeMap<usize, i32>;

#[derive(Debug)]
pub struct Jobs {
    jobs: JobMap,
    cur_id: usize,
}

impl Jobs {
    pub fn new() -> Jobs {
        Jobs { jobs: JobMap::new(), cur_id: 0 }
    }

    fn make_id(&mut self) -> usize {
        let ret = self.cur_id;
        self.cur_id += 1;
        ret
    }

    pub fn add(&mut self, pid: i32) -> usize {
        let id = self.make_id();
        self.jobs.insert(id, pid);
        id
    }

    pub fn iter(&self) -> ::std::collections::btree_map::Iter<usize, i32> {
        self.jobs.iter()
    }
}

pub struct Interp {
    sys_vars: RefCell<VarMap>,
    global_vars: RefCell<VarMap>,

    pub funcs: RefCell<FuncMap>,
    pub jobs: RefCell<Jobs>,
}

fn new_vec_init<T: Clone>(index: i64, def: T, val: T) -> Vec<T> {
    if index >= 0 {
        let index = index as usize;
        let mut ret = vec![def; index + 1];
        ret[index] = val;
        ret
    } else {
        let mut ret = vec![def; -index as usize];
        ret[0] = val;
        ret
    }
}

#[derive(Debug)]
pub enum Indexing<'a> {
    NoIndex,
    Offset(i64),
    Dict(&'a str),
    Range(Range),
}

impl<'a> Indexing<'a> {
    pub fn from_val(val: &'a Val) -> Result<Indexing, Val> {
        if let Some(i) = val.get_str() {
            if let Ok(i) = str::parse::<i64>(i) {
                Ok(Indexing::Offset(i))
            } else {
                Ok(Indexing::Dict(i))
            }
        } else if let Ok(rng) = Range::from_val(val) {
            Ok(Indexing::Range(rng))
        } else {
            Err(Val::err(RuntimeError::InvalidIndex(val.clone().into(),
                         "Index must be a scalar or range"), None))
        }
    }
}

impl Interp {
    pub fn new() -> Interp {
        Interp {
            sys_vars: HashMap::new().into(),
            global_vars: HashMap::new().into(),
            funcs: FuncMap::new().into(),
            jobs: Jobs::new().into()
        }
    }

    fn do_set(op: SetOp, id: &str, index: Indexing, val: Val, local_vars: &mut LocalVars) {
        use self::Val::*;

        fn apply_op(op: SetOp, cur: &mut Val, new: Val) {
            use self::SetOp::*;
            match op {
                Assign => *cur = new,
                AssignIfNull => if cur.is_void() {
                    *cur = new;
                },
                Suffix => match cur {
                    &mut Val::Tup(ref mut v) => {
                        v.push(new);
                    },
                    _ => {
                        let mut tmp = Val::void();
                        ::std::mem::swap(&mut tmp, cur);
                        *cur = Val::Tup(vec![tmp, new]);
                    },
                },
                Prefix => match cur {
                    &mut Val::Tup(ref mut v) => {
                        v.insert(0, new);
                    },
                    _ => {
                        let mut tmp = Val::void();
                        ::std::mem::swap(&mut tmp, cur);
                        *cur = Val::Tup(vec![new, tmp]);
                    },
                },
            }
        }

        use std::ops::DerefMut;

        fn apply_op_var_ref(op: SetOp, r: &VarRef, val: Val) {
            apply_op(op, r.get_mut().deref_mut(), val);
        }

        fn apply_op_void(op: SetOp, val: Val) -> Val {
            let mut new = Val::void();
            apply_op(op, &mut new, val);
            return new;
        }

        fn do_set_offset(op: SetOp, var: &VarRef, index: i64, val: Val) {
            let mut orig = var.get_mut();
            let mut n = None;
            match *orig {
                Tup(ref mut v) => {
                    if index >= 0 {
                        let index = index as usize;
                        if v.len() <= index {
                            v.resize(index + 1, Val::void())
                        }
                        //v[index] = val;
                        apply_op(op, &mut v[index], val);
                    } else {
                        let index = v.len() as i64 + index;
                        if index < 0 {
                            v.splice(0..0, ::std::iter::repeat(Val::void()).take(-index as usize));
                            apply_op(op, &mut v[0], val);
                        } else {
                            apply_op(op, &mut v[index as usize], val);
                        }
                    }
                },
                Str(_) => {
                    let val = apply_op_void(op, val);
                    n = Some(Tup(new_vec_init(index, Val::void(), val)));
                },
                _ => panic!("Attempted to set non-scalar or tuple: {:?}", val)
            }
            if let Some(n) = n {
                *orig = n;
            }
        }

        fn do_set_dict(op: SetOp, var: &VarRef, key: &str, val: Val) {
            let mut orig = var.get_mut();
            let mut err = false;
            let mut tuplefy = false;
            match *orig {
                Tup(ref mut v) => {
                    for cur in v {
                        match *cur {
                            Tup(ref mut v) if v.len() == 2 &&
                                    v[0].get_str().map_or(false, |x| x == key) => {
                                apply_op(op, &mut v[1], val);
                                return;
                            },
                            _ => {},
                        }
                    }
                },
                Str(_) => {
                    tuplefy = true;
                },
                _ => err = true,
            }
            if err { panic!("Attempted to set non-scalar or tuple: {:?}", val); }
            if tuplefy {
                let mut o = Val::void();
                ::std::mem::swap(&mut o, &mut *orig);
                *orig = Tup(vec![o]);
            }
            if let Tup(ref mut v) = *orig {
                let val = apply_op_void(op, val);
                v.push(Tup(vec![Val::str(key), val]));
            } else {
                unreachable!();
            }
        }

        fn do_set_range(op: SetOp, var: &VarRef, l: i64, r: i64, val: Val) {
            if let SetOp::Assign = op {
                fn wrap_index(index: i64, len: usize) -> i64 {
                    if index >= 0 {
                        index
                    } else {
                        len as i64 + index
                    }
                }

                let val_into_iter = |val| {
                    let iter = match val {
                        Val::Tup(val) => val.into_iter(),
                        Val::Ref(_) => vec!(Val::Embed(Box::new(val))).into_iter(),
                        _ => vec!(val).into_iter(),
                    };
                    iter
                };

                let mut mut_ref = var.get_mut();
                let cur = mut_ref.deref_mut();
                match cur {
                    &mut Val::Tup(ref mut cur) => {
                        let n = cur.len() as i64;
                        let l = wrap_index(l, n as usize);
                        let r = wrap_index(r, n as usize);
                        let iter = val_into_iter(val);
                        use std::iter::repeat;
                        if l < 0 {
                            if r < 0 {
                                let iter = iter.chain(repeat(Val::void()).take((-r - 1) as usize));
                                cur.splice(0..0, iter);
                            } else if r < n {
                                cur.splice(0...r as usize, iter);
                            } else {
                                *cur = iter.collect();
                            }
                        } else if l < n {
                            if r < n {
                                cur.splice(l as usize...r as usize, iter);
                            } else {
                                cur.splice(l as usize..n as usize, iter);
                            }
                        } else {
                            let iter = repeat(Val::void()).take((l - n) as usize).chain(iter);
                            cur.splice(n as usize..n as usize, iter);
                        }
                    },
                    _ => {
                        unimplemented!();
                    }
                }
            } else {
                unimplemented!();
            }
        }

        if let Some(var) = local_vars.get(id) {
            //println!("Set {:?} from {:?} to {:?} using {:?}", id, old_val, val, op);
            match index {
                Indexing::NoIndex => apply_op_var_ref(op, var, val),
                Indexing::Offset(index) => do_set_offset(op, var, index, val),
                Indexing::Dict(key) => do_set_dict(op, var, key, val),
                Indexing::Range(Range::WithinInt(l, r)) => do_set_range(op, var, l, r, val),
                _ => unimplemented!(),
            }
            return; // Use this instead of "else" to make borrow checker happy
        }

        let val = apply_op_void(op, val);
        //println!("Implicit bind {:?} to {:?}", id, val);
        local_vars.bind(id, match index {
            Indexing::NoIndex => val,
            Indexing::Offset(index) => Tup(new_vec_init(index, Val::void(), val)),
            Indexing::Dict(key) => Tup(vec![Tup(vec![Val::str(key), val])]),
            _ => unimplemented!(),
        });
    }

    fn get_varmap(&self, scope: ImportScope) -> &RefCell< VarMap> {
        match scope {
            ImportScope::Sys => &self.sys_vars,
            ImportScope::Global => &self.global_vars,
        }
    }

    fn lookup_import(&self, scope: ImportScope, name: &str, assign: Option<(SetOp, Val)>) -> VarRef {
        let mut vars = self.get_varmap(scope).borrow_mut();
        if let Some(r) = vars.get(name) {
            if let Some((s, v)) = assign {
                if let Some(v) = v.get_str() {
                    match s {
                        SetOp::Assign => r.set(Val::str(v)),
                        SetOp::Prefix => r.set(Val::Str(v.to_string() + r.get().get_str().unwrap())),
                        SetOp::Suffix => r.set(Val::Str(r.get().get_str().unwrap().to_string() + v)),
                        _ => {},
                    }
                } else {
                    panic!("sys and global vars must be scalar string");
                }
            }
            return r.clone()
        }
        if let Some((_, v)) = assign {
            if let Some(v) = v.get_str() {
                return vars.entry(name.to_string()).or_insert(VarRef::new(Val::str(v))).clone();
            }
            panic!("sys and global vars must be scalar string");
        }
        panic!("Unknown sys or global var must be initialized");
    }

    fn call_op_bool(&self, val: Val, span: Span, l: &mut LocalVars) -> Val {
        let mut v = Vec::with_capacity(2);
        v.push(Val::Str("op::bool".to_string()));
        v.push(val);
        v[1].eval();
        let t = Val::Tup(v);
        let c = self.try_call(t, span, l);
        return match c {
            Ok(val) => val,
            Err(val) => val.take_tup().unwrap().into_iter().nth(1).unwrap(),
        };
    }

    fn if_cond(&self, r: &mut LocalVars, cond: &ExprS, has_else: bool) -> Result<bool, (Val, Control)> {
        match *cond {
            ExprS(Expr::Let(ref b, ref e), _span) => {
                let mut val = self.from_expr(&*e, r);
                if val.1.stops_exec() {
                    return Err(val);
                }
                val.0.eval();
                r.enter_scope();
                if b.subsumes(&val.0) == Subsumption::Contains {
                    b.do_match_unchecked(val.0.into(), r);
                    return Ok(true);
                } else {
                    r.exit_scope();
                    if has_else { r.enter_scope(); }
                    return Err(val);
                }
            },
            ref e => {
                let span = e.1;
                let (val, con) = self.exec_stmt(e, r);
                if con.stops_exec() {
                    return Err((val, con));
                }
                let val = self.call_op_bool(val, span, r);
                match Self::val_is_truthy(&val) {
                    Some(true) => {
                        r.enter_scope();
                        return Ok(true);
                    },
                    Some(false) => {
                        if has_else { r.enter_scope(); }
                        return Ok(false);
                    },
                    None => {
                        panic!("If condition not boolean (1 or 0) [{:?}]", val);
                    },
                }
            },
        };
    }

    fn do_if(&self, r: &mut LocalVars, cond: &ExprS, then: &Vec<ExprS>, el: &Option<Vec<ExprS>>) -> (Val, Control) {
        //println!("{:?}", e);
        let mut res = (Val::void(), Control::Done);
        let has_else = el.is_some() && el.as_ref().unwrap().len() > 0;
        match self.if_cond(r, cond, has_else) {
            Ok(b) => {
                if b {
                    res = self.exec_stmt_list(then, r);
                    r.exit_scope();
                } else if has_else {
                    res = self.exec_stmt_list(el.as_ref().unwrap(), r);
                    r.exit_scope();
                }
            }
            Err(e) => {
                return e;
            }
        }
        res
    }

    fn do_while(&self, r: &mut LocalVars, cond: &ExprS, lo: &Vec<ExprS>) -> (Val, Control) {
        //println!("{:?}", e);
        let mut res = (Val::void(), Control::Done);
        loop {
            match self.if_cond(r, cond, false) {
                Ok(b) => {
                    if b {
                        res = self.exec_stmt_list(lo, r);
                        r.exit_scope();
                        if res.1.breaks_loops() {
                            res.1.clear_breaks();
                            break
                        }
                    } else { break }
                },
                Err(e) => return e,
            }
        }
        res
    }

    fn do_lambda(&self, r: &mut LocalVars,
                 c: &Vec<(String, Option<ExprS>)>,
                 p: &Pat, b: &RefCell<Option<Vec<ExprS>>>) -> (Val, Control) {
        use self::Val::*;

        //println!("Lambda captures: {:?}", c);
        if b.borrow_mut().is_some() {
            let mut body = None;
            ::std::mem::swap(&mut body, &mut *b.borrow_mut());
            self.funcs.borrow_mut().reg(Func::user(p.clone(), body.unwrap()));
        }
        let name = if let &Pat::Tup(ref v) = p {
            if let &Pat::Str(ref s) = &v[0] {
                Str(s.clone())
            } else { unreachable!() }
        } else { unreachable!() };
        if c.len() == 0 {
            (name, Control::Done)
        } else {
            let mut ret = Vec::with_capacity(c.len() + 1);
            ret.push(name);
            for ref x in c {
                match **x {
                    (ref i, None) => {
                        let v = r.get(i).expect("Capturing unbound variable").get();
                        ret.push(v);
                    }
                    (_, Some(ref e)) => {
                        let (v, c) = self.from_expr(e, r);
                        if c.stops_exec() {
                            return (v, c)
                        }
                        ret.push(v);
                    }
                }
            }
            (Val::Tup(ret), Control::Done)
        }
    }

    fn do_match(&self, r: &mut LocalVars, e: &ExprS, cases: &Vec<(Pat, ExprS)>) -> (Val, Control) {
        let val = self.from_expr(e, r);
        if val.1.stops_exec() {
            return val
        }
        for &(ref pat, ref body) in cases {
            if pat.subsumes(&val.0) == Subsumption::Contains {
                r.enter_scope();
                pat.do_match_unchecked(val.0.into(), r);
                let res = self.exec_stmt(body, r);
                r.exit_scope();
                return res;
            }
        }
        (val.0, Control::Done)
    }

    fn do_for(&self, r: &mut LocalVars, pat: &Pat, iter: &ExprS, body: &Vec<ExprS>) -> (Val, Control) {
        let mut res = (Val::void(), Control::Done);
        let ispan = iter.1;
        let val = self.from_expr(iter, r);
        if val.1.stops_exec() {
            return val
        }
        let call_iterate = Val::Tup(vec![Val::str("iter"), val.0]);
        match self.try_call(call_iterate, ispan, r) {
            Ok(val) => {
                let mut cur = val;
                loop {
                    {
                        let v = cur.get_tup().unwrap();
                        if v.len() < 2 { break; }
                        if pat.subsumes(&v[1]) == Subsumption::Contains {
                            r.enter_scope();
                            pat.do_match_unchecked((&v[1]).into(), r);
                            res = self.exec_stmt_list(body, r);
                            r.exit_scope();
                            if res.1.breaks_loops() {
                                res.1.clear_breaks();
                                break
                            }
                        }
                    }
                    let call_next = Val::Tup(vec![Val::str("next"), cur]);
                    match self.try_call(call_next, ispan, r) {
                        Ok(val) => {
                            cur = val;
                        },
                        Err(_) => break,
                    }
                }
            },
            Err(val) => {
                let val : Val = val.take_tup().unwrap().into_iter().nth(1).unwrap();
                Cow::from(val).for_each_shallow(&mut |val: Cow<Val>| {
                    if pat.subsumes(&*val) == Subsumption::Contains {
                        r.enter_scope();
                        pat.do_match_unchecked(val, r);
                        res = self.exec_stmt_list(body, r);
                        r.exit_scope();
                        if res.1.breaks_loops() {
                            res.1.clear_breaks();
                            return false
                        }
                    }
                    return true;
                });
            },
        };

        res
    }

    fn do_string(&self, s: &str, _: &mut LocalVars) -> (Val, Control) {
        use glob::{glob_with, MatchOptions};
        let options = MatchOptions {
            case_sensitive: true,
            require_literal_separator: true,
            require_literal_leading_dot: true,
        };
        match glob_with(s, &options) {
            Ok(list) => {
                let names: Vec<_> = list.filter_map(|path| path.ok()).map(|path| {
                    Val::Str(path.to_string_lossy().into())
                }).collect();
                match names.len() {
                    0 => (Val::Str(s.into()), Control::Done),
                    1 => (names.into_iter().next().unwrap(), Control::Done),
                    _ => (Val::Embed(Box::new(Val::Tup(names))), Control::Done),
                }
            },
            Err(_) => (Val::Str(s.into()), Control::Done),
        }

    }

    fn do_xstring(&self, v: &Vec<ExprS>, r: &mut LocalVars) -> (Val, Control) {
        let mut ret = "".to_string();
        for e in v {
            let (mut val, c) = self.from_expr(e, r);
            if c.stops_exec() {
                return (Val::void(), c)
            }
            val.eval();
            match val {
                Val::Str(s) => {
                    ret.push_str(s.as_ref());
                }
                Val::Tup(_) => {
                    let mut count = 0;
                    Cow::from(val).for_each(&mut |s: Cow<str>, _| {
                        if count > 0 { ret.push(' '); }
                        ret.push_str(&*s);
                        count += 1;
                        return true
                    });
                }
                Val::Error(..) => return (val, Control::Done),
                _ => unreachable!(),
            }
        }
        (Val::Str(ret), Control::Done)
    }

    fn do_background(&self, e: &ExprS, r: &mut LocalVars) -> (Val, Control) {
        use nix::unistd::{fork, ForkResult};

        match fork() {
            Ok(ForkResult::Parent { child, .. }) => {
                let job_id = self.jobs.borrow_mut().add(child);
                (Val::Tup(vec![Val::str("Job"), Val::Str(job_id.to_string()),
                                                Val::Str(child.to_string())]),
                     Control::Done)
            },
            Ok(ForkResult::Child) => {
                let ret = self.exec_stmt(e, r);
                (ret.0, Control::Exit)
            },
            Err(e) => (Val::err_string(format!("{}", e)), Control::Done),
        }
    }

    pub fn from_expr(&self, e: &ExprS, r: &mut LocalVars) -> (Val, Control) {
        use self::Expr::*;
        use self::Val::*;

        //println!("from_expr: {:?}", e);
        match e.0 {
            Tuple(_, ref v) => {
                let mut is_new_err = false;
                let mut ret = vec![];
                for x in v.iter().enumerate() {
                    match self.from_expr(x.1, r) {
                        (e @ Val::Error(..), c) => return (e, c),
                        (v, Control::Done) => {
                            if x.0 == 0 && v.get_str().unwrap_or("") == "Err!" {
                                is_new_err = true
                            } else {
                                ret.push(v)
                            }
                        },
                        (v, c) => return (v, c),
                    }
                }
                if is_new_err {
                    (Val::custom_err(ret, Some(e.1)), Control::Done)
                } else {
                    (Tup(ret), Control::Done)
                }
            },
            Ident(ref s) => (Str(s.clone()), Control::Done),
            String(ref s) => self.do_string(s, r),
            LString(ref s) => (Str(s.clone()), Control::Done),
            XString(ref v) => self.do_xstring(v, r),
            Block(ref b) => {
                r.enter_scope();
                let res = self.exec_stmt_list(b, r);
                r.exit_scope();
                res
            },
            Lambda(ref c, ref p, ref b) => self.do_lambda(r, c, p, b),
            Var(m, ref n) => (self.get_var_ref(m, n, r), Control::Done),
            Exec(m, ref n, _) => self.get_exec(m, n, r),
            Call(m, ref n, _) => self.do_call(m, n, r),
            Expr::Range(ref r) => match ::rush_parser::ast::ASTRange::from_ast_range(r.into()) {
                Ok(r) => (r.as_val(), Control::Done),
                Err(x) => (Val::err(RuntimeError::ParseError(x), Some(e.1)), Control::Done),
            },
            Expr::Rex(ref r) => {
                ((&r.0).into(), Control::Done)
            }
            If{ref cond, ref then, ref el} => self.do_if(r, cond, then, el),
            While{ref cond, ref lo} => self.do_while(r, cond, lo),
            Match{ref val, ref cases} => self.do_match(r, val, cases),
            For{ref pat, ref iter, ref lo} => self.do_for(r, pat, iter, lo),
            Read(ref ids) => self.do_read(ids, r),
            _ => unimplemented!(),
        }
    }

    fn do_call(&self, m: SubsMode, n: &ExprS, l: &mut LocalVars) -> (Val, Control) {
        let (val, con) = self.exec_stmt(n, l);
        if con.stops_exec() {
            return (val, con)
        }
        /*
        val.into_with_val(|val| {
            use std::borrow::Borrow;

            if let &Val::Str(ref s) = val.borrow() {
                return (Self::get_var_ref_id(m, s, n.1, l), con);
            }
        })*/
            match m {
                SubsMode::Insert => (val, con),
                SubsMode::Embed => (Val::Embed(Box::new(val)), con),
                _ => unimplemented!(),
            }
    }

    fn get_exec(&self, _: SubsMode, n: &ExprS, l: &mut LocalVars) -> (Val, Control) {
        use std::io::{Read, Seek, SeekFrom};
        use std::os::unix::io::AsRawFd;

        let mut tmpf = ::tempfile::tempfile().unwrap();

        let fd = tmpf.as_raw_fd();

        let oldout = dup(1).unwrap();
        dup2(fd, 1).unwrap();

        let n = self.exec_stmt(n, l);
        if n.1.stops_exec() {
            return n
        }

        dup2(oldout, 1).unwrap();
        close(oldout).unwrap();

        tmpf.seek(SeekFrom::Start(0)).unwrap();

        let mut buf = String::new();
        tmpf.read_to_string(&mut buf).unwrap();

        (Val::str(buf), Control::Done)
    }

    fn get_var_ref(&self, m: SubsMode, n: &ExprS, r: &mut LocalVars) -> Val {
        use self::Expr::*;
        match n.0 {
            Ident(ref id) => self.get_var_ref_id(m, id, n.1, r),
            Var(_, ref e) => {
                let var = self.get_var_ref(SubsMode::Insert, e, r);
                var.with_val(|val| {
                    match *val {
                        Val::Str(ref s) => self.get_var_ref_id(m, s, n.1, r),
                        _ => self.call(val.clone(), n.1, r),
                    }
                })
            },
            _ => panic!("Invalid variable identifier: {:?}", n),
        }
    }

    fn get_var_ref_id(&self, m: SubsMode, id: &str, span: Span, r: &mut LocalVars) -> Val {
        let v = r.get(id);
        let r = match v {
            Some(r) => Val::Ref(r.clone()),
            None => return Val::err(RuntimeError::UnboundVariable(id.into()), Some(span)),
        };
        //println!("var: {:?}", r);
        match m {
            SubsMode::Insert => r,
            SubsMode::Embed => Val::Embed(Box::new(r)),
            _ => unimplemented!(),
        }
    }

    pub fn try_call(&self, val: Val, span: Span, l: &mut LocalVars) -> Result<Val, Val> {
        let val = match val {
            Val::Tup(_) => val,
            Val::Error(..) => return Ok(val),
            _ => Val::Tup(vec![val]),
        };
        let lookup = { self.funcs.borrow().lookup(val) };
        match lookup {
            Ok((mut locals, body)) => {
                let mut val = match body {
                    FuncBody::BuiltIn(f) => {
                        f(self, &mut locals)
                    },
                    FuncBody::Macro(m) => {
                        m(self, l, locals.last().unwrap().take())
                    },
                    FuncBody::User(ref vec) => {
                        let ret = self.exec_stmt_list(vec, &mut locals).0;
                        locals.exit_scope();
                        ret
                    },
                };
                match val {
                    Val::Error(ref mut e) => {
                        if let Some(&mut(_, _, ref mut spans)) = Rc::get_mut(e) {
                            spans.push(span);
                        }
                    },
                    _ => {},
                }
                Ok(val)
            },
            Err(val) => return Err(val),
        }
    }

    pub fn call(&self, val: Val, span: Span, l: &mut LocalVars) -> Val {
        let mut ret = match self.try_call(val, span, l) {
            Ok(val) => val,
            Err(val) => {
                let val = Val::Tup(vec![Val::Str("system".into()), Val::Embed(Box::new(val))]);
                self.try_call(val, span, l).expect("No matching fn")
            }
        };
        ret.eval();
        ret
    }

    pub fn val_is_truthy(val: &Val) -> Option<bool> {
        match val.get_str() {
            Some("1") => Some(true),
            Some("0") => Some(false),
            _ => None,
        }
    }

    pub fn exec_stmt(&self, stmt_s: &ExprS, local_vars: &mut LocalVars) -> (Val, Control) {
        let &ExprS(ref stmt, span) = stmt_s;
        match *stmt {
            Expr::Let(ref bind, ref v) => {
                let mut val = self.from_expr(&*v, local_vars);
                if val.1.stops_exec() {
                    return val;
                }
                val.0.eval();
                //println!("Bind {:?} to {:?}", bind, val);
                bind.do_match_unchecked(val.0.into(), local_vars);
                (Val::void(), Control::Done)
            },
            Expr::Set(op, ref n, ref v) => {
                let mut val = self.from_expr(&*v, local_vars);
                if val.1.stops_exec() {
                    return val;
                }
                val.0.eval();
                //println!("Bind {:?} to {:?}", n, val);
                match &**n {
                    &ExprS(Expr::Ident(ref id), _) => {
                        Self::do_set(op, id, Indexing::NoIndex, val.0, local_vars);
                    },
                    &ExprS(Expr::Index((ref id, _), ref index), _) => {
                        let (index, con) = self.from_expr(&*index, local_vars);
                        return index.with_val(move |index| {
                            if con.stops_exec() {
                                return (Val::void(), con);
                            }
                            match Indexing::from_val(&index) {
                                Ok(index) => Self::do_set(op, id, index, val.0, local_vars),
                                Err(err) => return (err, Control::Done),
                            };
                            (Val::void(), Control::Done)
                        })
                    },
                    _ =>
                        panic!("Left-hand-side of assignment not an identifier"),
                }
                (Val::void(), Control::Done)
            },
            Expr::Import(scope, ref name, ref rename, ref assign) => {
                if let Some(name) = name.get_ident() {
                    let assign = match assign {
                        &Some((op, ref e)) => {
                            let mut val = self.from_expr(&*e, local_vars);
                            if val.1.stops_exec() {
                                return val;
                            }
                            val.0.eval();
                            Some((op, val.0))
                        },
                        &None => None,
                    };
                    let var = self.lookup_import(scope, name, assign);
                    if let &Some(ref rename) = rename {
                        if let Some(rename) = rename.get_ident() {
                            local_vars.import(rename, var);
                        } else {
                            panic!("Expected identifier after :");
                        }
                    } else {
                        local_vars.import(name, var);
                    }
                } else {
                    panic!("Expected identifier");
                }
                (Val::void(), Control::Done)
            },
            Expr::FuncDec(ref pat, ref b) => {
                if b.borrow_mut().is_some() {
                    let mut body = None;
                    ::std::mem::swap(&mut body, &mut *b.borrow_mut());
                    if !self.funcs.borrow_mut().reg(Func::user(pat.clone(), body.unwrap())) {
                        return (Val::err_string(format!("Failed to add function {:?} due to ambiguity", pat)), Control::Done);
                    }
                }
                (Val::void(), Control::Done)
            },
            Expr::Return(None) => {
                (Val::void(), Control::Return)
            },
            Expr::Return(Some(ref expr)) => {
                let (val, _) = self.from_expr(expr, local_vars);
                (val, Control::Return)
            },
            Expr::Break(None) => {
                (Val::void(), Control::Break)
            },
            Expr::Break(Some(ref expr)) => {
                let (val, _) = self.from_expr(expr, local_vars);
                (val, Control::Break)
            },
            Expr::Continue(None) => {
                (Val::void(), Control::Continue)
            },
            Expr::Continue(Some(ref expr)) => {
                let (val, _) = self.from_expr(expr, local_vars);
                (val, Control::Continue)
            },
            Expr::Tuple(..) | Expr::Ident(..) | Expr::String(..) | Expr::XString(..) |
                Expr::LString(..) | Expr::Exec(..) | Expr::Call(..) | Expr::Var(..) | Expr::Lambda(..) => {
                let (val, con) = self.from_expr(stmt_s, local_vars);
                //println!("Will call {:?} => {:?}", stmt, val);
                if con.stops_exec() {
                    (val, con)
                } else {
                    let val = self.call(val, span, local_vars);
                    (val, Control::Done)
                }
            },
            Expr::Nop => { (Val::void(), Control::Done) },
            Expr::If{..} | Expr::While{..} | Expr::Match{..} | Expr::For{..} | Expr::Block(..) | Expr::Read(..) => {
                self.from_expr(stmt_s, local_vars)
            },
            Expr::Background(ref expr) => {
                self.do_background(&*expr, local_vars)
            },
            Expr::Pipe(ref stages, ref outfile) => {
                self.do_pipe(stages, outfile, local_vars)
            },
            Expr::And(ref lhs, ref rhs) => {
                self.do_and_or(&*lhs, &*rhs, false, local_vars)
            },
            Expr::Or(ref lhs, ref rhs) => {
                self.do_and_or(&*lhs, &*rhs, true, local_vars)
            },
            Expr::Index(..) | Expr::Range(..) | Expr::Rex(..) => unreachable!(),
            Expr::Manip(..) => unimplemented!(),
        }
    }

    fn do_and_or(&self, lhs: &ExprS, rhs: &ExprS, is_or: bool, local_vars: &mut LocalVars) -> (Val, Control) {
        let (val, con) = self.exec_stmt(lhs, local_vars);
        if con.stops_exec() {
            return (val, con)
        }
        let b = self.call_op_bool(val.clone(), lhs.1, local_vars);
        match Self::val_is_truthy(&b) {
            Some(b) => {
                if b ^ is_or {
                    self.exec_stmt(rhs, local_vars)
                } else {
                    (val, con)
                }
            },
            None => {
                (Val::err(RuntimeError::BadValType(Box::new(b), "No known conversion to boolean"), Some(lhs.1)), con)
            },
        }
    }

    fn do_pipe(&self, stages: &Vec<ExprS>, outfile: &Option<Box<ExprS>>, local_vars: &mut LocalVars) -> (Val, Control) {
        let mut pipeline = Pipeline::create(stages);
        let ret = outfile.as_ref().map(|outfile| {
            self.from_expr(&**outfile, local_vars)
        });
        if let Some((ref val, ref con)) = ret {
            if con.stops_exec() {
                return (val.clone(), *con)
            }
        }
        let (val, con) = pipeline.exec(&self, ret.and_then(|x| x.0.get_string()), local_vars);
        (val, con)
    }

    fn do_read(&self, ids: &Vec<ExprS>, local_vars: &mut LocalVars) -> (Val, Control) {

        if ids.len() == 0 {
            return (Val::false_(), Control::Done);
        }

        use std::io::{self, BufRead};

        let stdin = io::stdin();
        let ret = match stdin.lock().lines().next() {
            Some(line) => match line {
                Ok(line) => {
                    let mut do_bind = |id: &ExprS, s: &str| {
                        if let Expr::Ident(ref id) = id.0 {
                            local_vars.bind(id.clone(), Val::str(s));
                        } else {
                            panic!("Invalid argument to read: {:?}", id);
                        }
                    };
                    let mut remainder = (&line[..]).trim_left();
                    for id in ids.iter().take(ids.len() - 1) {
                        let word = remainder.split_whitespace().take(1).next().unwrap_or("");
                        do_bind(id, word);
                        remainder = (&remainder[word.len()..]).trim_left();
                    }
                    do_bind(ids.last().unwrap(), remainder.trim_right());
                    (Val::true_(), Control::Done)
                },
                Err(err) => {
                    (Val::err_string(format!("{:?}", err)), Control::Done)
                },
            },
            None => (Val::false_(), Control::Done),
        };
        return ret;
    }

    pub fn exec_stmt_list(&self, stmt_list: &Vec<ExprS>, local_vars: &mut LocalVars) -> (Val, Control) {
        use self::Control::*;

        let mut ret = Val::void();
        for ref stmt in stmt_list {
            ret.unhandled();
            let (v, c) = self.exec_stmt(stmt, local_vars);
            match c {
                Return | Break | Continue | Exit => return (v, c),
                Done => {
                    ret = v
                }
            }
        }
        return (ret, Control::Done)
    }

    pub fn exec(&self, stmt_list: &Vec<ExprS>) -> (Val, Control) {
        let mut local_vars = LocalVars::new();
        local_vars.enter_scope();
        let ret = self.exec_stmt_list(stmt_list, &mut local_vars);
        ret.0.unhandled();
        local_vars.exit_scope();
        ret
    }
}

use nix::unistd::{fork, ForkResult, pipe, dup, dup2, close};
use nix::sys::wait::{waitpid, WaitStatus};

#[derive(Debug)]
enum StageStatus {
    Initialized,
    Background(i32),
    Foreground,
    Completed(WaitStatus),
}

#[derive(Debug)]
struct Stage<'a> {
    code: &'a ExprS,
    status: StageStatus,
}

impl<'a> Stage<'a> {
    fn create(code: &'a ExprS) -> Stage {
        Stage{code, status: StageStatus::Initialized}
    }
}

#[derive(Debug)]
struct Pipeline<'a> {
    stages: Vec<Stage<'a>>,
}

impl<'a> Pipeline<'a> {
    fn create(stages: &'a Vec<ExprS>) -> Pipeline {
        Pipeline{ stages: stages.into_iter().map(|x| Stage::create(x)).collect() }
    }

    fn exec<S: ToString>(&mut self, interp: &Interp, outfile: Option<S>, local_vars: &mut LocalVars) -> (Val, Control) {
        let mut use_input = 0;
        let n = self.stages.len();
        if n == 0 {
            return (Val::void(), Control::Done);
        }
        for ref mut s in self.stages.iter_mut().take(n - 1) {
            let (pread, pwrite) = pipe().unwrap();
            let (input, output) = (use_input, pwrite);
            use_input = pread;
            match fork() {
                Ok(ForkResult::Parent { child, .. }) => {
                    s.status = StageStatus::Background(child);
                    if input != 0 {
                        close(input).unwrap();
                    }
                    if output != 1 {
                        close(output).unwrap();
                    }
                },
                Ok(ForkResult::Child) => {
                    if input != 0 {
                        dup2(input, 0).unwrap();
                        close(input).unwrap();
                    }
                    if output != 1 {
                        dup2(output, 1).unwrap();
                        close(output).unwrap();
                    }
                    let (val, _) = interp.exec_stmt(s.code, local_vars);
                    if let Val::Tup(ref v) = val {
                        if v.len() == 2 && v[0].get_str() == Some("Status") {
                            if let Some(v) = v[1].get_str() {
                                if let Ok(x) = str::parse::<i32>(v) {
                                    ::std::process::exit(x);
                                }
                            }
                        }
                    }
                    ::std::process::exit(0);
                },
                Err(_) => panic!("Fork failed!"),
            }
        }
        let (val, con) = {
            let last_stage = self.stages.last_mut().unwrap();

            let oldin = if use_input != 0 {
                let oldin = dup(0).unwrap();
                dup2(use_input, 0).unwrap();
                close(use_input).unwrap();
                Some(oldin)
            } else {
                None
            };

            let oldout = if let Some(outfile) = outfile {
                let oldout = dup(1).unwrap();

                use std::fs::File;
                use std::os::unix::io::IntoRawFd;

                let fout = File::create(outfile.to_string()).unwrap();
                let fd = fout.into_raw_fd();

                dup2(fd, 1).unwrap();
                close(fd).unwrap();
                Some(oldout)
            } else {
                None
            };

            last_stage.status = StageStatus::Foreground;
            let ret = interp.exec_stmt(last_stage.code, local_vars);

            if let Some(oldin) = oldin {
                dup2(oldin, 0).unwrap();
                close(oldin).unwrap();
            }

            if let Some(oldout) = oldout {
                dup2(oldout, 1).unwrap();
                close(oldout).unwrap();
            }

            ret
        };
        for ref mut s in self.stages.iter_mut() {
            if let StageStatus::Background(pid) = s.status {
                let status = waitpid(pid, None).unwrap();
                s.status = StageStatus::Completed(status);
            }
        }
        return (val, con);
    }
}
