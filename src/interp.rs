use rush_parser::ast::{ExprS, Expr, SetOp, ImportScope, SubsMode, Span, ManOp};
use rush_pat::pat::Pat;
use rush_rt::vars::{VarRef, LocalVars, Resolver, Binder, Scoped};
use rush_rt::val::{Val, InternalIterable};
use rush_rt::error::{RuntimeError};
use rush_rt::pat::{ValMatcher, ValArray};
use rush_rt::range::{RangeExt};
use rush_pat::subsume::{Subsumes, Subsumption};
use std::collections::{HashMap};
use std::borrow::{Cow, Borrow, BorrowMut};
use func::{Control, Func, FuncBody, FuncMap};
use std::cell::RefCell;
use std::rc::Rc;
use nix::unistd::{dup, dup2, close};
use jobs::Jobs;
use pipeline::Pipeline;

type VarMap = HashMap<String, VarRef>;

pub struct Interp {
    global_vars: VarMap,

    pub funcs: FuncMap,
    pub jobs: Jobs,
}

impl Interp {
    pub fn new() -> Interp {
        Interp {
            //sys_vars: HashMap::new().into(),
            global_vars: HashMap::new().into(),
            funcs: FuncMap::new().into(),
            jobs: Jobs::new().into(),
        }
    }

    /*
    fn get_varmap(&self, scope: ImportScope) -> &RefCell< VarMap> {
        match scope {
            ImportScope::Sys => &self.sys_vars,
            ImportScope::Global => &self.global_vars,
        }
    }*/

    fn lookup_import(&mut self, scope: ImportScope, name: &str, options: Option<Val>) -> VarRef {
        match scope {
            ImportScope::Sys => {
                let delim = options.and_then(|x| x.get_1char());
                return VarRef::using(::rush_rt::vars::EnvOps::new(name, delim));
            },
            ImportScope::Global => {
                if options.is_some() {
                    panic!("global variables do not support delimiter options");
                }
                if let Some(r) = self.global_vars.get(name) {
                    return r.clone()
                }
                return self.global_vars.entry(name.to_string()).or_insert(VarRef::new(Val::void())).clone();
            },
        }
    }

    fn call_op_bool(&mut self, val: Val, span: Span, l: &mut LocalVars) -> Val {
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

    fn if_cond(&mut self, r: &mut LocalVars, cond: &ExprS, has_else: bool) -> Result<bool, (Val, Control)> {
        match *cond {
            ExprS(Expr::Let(ref b, ref e), _span) => {
                let mut val = self.from_expr(&*e, r);
                if val.1.stops_exec() {
                    return Err(val);
                }
                val.0.eval();
                r.enter_scope();
                if b.subsumes(&val.0).same_or_contains() {
                    b.do_match_unchecked(val.0.into(), r);
                    return Ok(true);
                } else {
                    r.exit_scope();
                    if has_else { r.enter_scope(); }
                    return Ok(false);
                }
            },
            ExprS(Expr::Recv(ref p), _span) => {
                r.enter_scope();
                let (val, con) = self.do_recv(p, r, true);
                if val.is_true() {
                    return Ok(true);
                } else {
                    r.exit_scope();
                    if has_else { r.enter_scope(); }
                    return Err((val, con));
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

    fn do_if(&mut self, r: &mut LocalVars, cond: &ExprS, then: &Vec<ExprS>, el: &Option<Vec<ExprS>>) -> (Val, Control) {
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

    fn do_while(&mut self, r: &mut LocalVars, cond: &ExprS, lo: &Vec<ExprS>) -> (Val, Control) {
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

    fn do_lambda(&mut self, r: &mut LocalVars,
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

    fn do_match(&mut self, r: &mut LocalVars, e: &ExprS, cases: &Vec<(Pat, ExprS)>) -> (Val, Control) {
        let (val, con) = self.from_expr(e, r);
        if con.stops_exec() {
            return (val, con)
        }
        for &(ref pat, ref body) in cases {
            if pat.subsumes(&val).same_or_contains() {
                r.enter_scope();
                pat.do_match_unchecked(val.into(), r);
                let ret = self.exec_stmt(body, r);
                r.exit_scope();
                return ret;
            }
        }
        (val, con)
    }

    fn do_match_all(&mut self, r: &mut LocalVars, e: &ExprS, cases: &Vec<(Pat, ExprS)>) -> (Val, Control) {
        let (val, con) = self.from_expr(e, r);
        if con.stops_exec() {
            return (val, con)
        }
        let mut ret = vec![];
        for &(ref pat, ref body) in cases {
            if pat.subsumes(&val).same_or_contains() {
                r.enter_scope();
                pat.do_match_unchecked((&val).into(), r);
                let (val, mut con) = self.exec_stmt(body, r);
                r.exit_scope();
                if con.breaks_loops() {
                    con.clear_breaks();
                    return (val, con)
                }
                ret.push(val);
            }
        }
        (Val::Tup(ret), con)
    }

    fn do_consume(&mut self, r: &mut LocalVars, e: &ExprS, cases: &Vec<(Pat, ExprS)>) -> (Val, Control) {
        let (val, con) = self.from_expr(e, r);
        if con.stops_exec() {
            return (val, con)
        }
        if let Ok(mut vec) = val.take_tup() {
            let mut i = 0;
            'outer: while i < vec.len() {
                for &(ref pat, ref body) in cases {
                    let mut plen = pat.req_len();
                    if pat.has_wild() {
                        plen = vec.len() - i;
                    }
                    if i + plen <= vec.len() {
                        let result = if plen == 1 {
                            pat.subsumes(&vec[i])
                        } else {
                            pat.subsumes(&ValArray(&vec[i..(i + plen)]))
                        };
                        if result.same_or_contains() {
                            use std::iter::repeat;
                            let val : Vec<_> = vec.splice(i..(i + plen), repeat(Val::void()).take(plen)).collect();
                            let val = if val.len() == 1 {
                                val.into_iter().next().unwrap()
                            } else {
                                Val::Tup(val.into())
                            };
                            r.enter_scope();
                            pat.do_match_unchecked(Cow::Owned(val), r);
                            let (v, mut con) = self.exec_stmt(body, r);
                            r.exit_scope();
                            if con.breaks_loops() {
                                con.clear_breaks();
                                return (v, con)
                            }
                            i += plen;
                            if con == Control::Continue {
                                match v {
                                    Val::Tup(vt) => {vec.splice(i..i, vt.into_iter());},
                                    Val::Error(_) => return (v, Control::Done),
                                    _ => {vec.insert(i, v);},
                                }
                            };
                            continue 'outer;
                        }
                    }
                }
                break
            }
            return (Val::Tup(vec.drain(i..).collect()), Control::Done)
        }
        (Val::void(), Control::Done)
    }

    fn do_for(&mut self, r: &mut LocalVars, pat: &Pat, val: &ExprS, body: &Vec<ExprS>) -> (Val, Control) {
        let mut res = (Val::void(), Control::Done);
        let val = self.from_expr(val, r);
        if val.1.stops_exec() {
            return val
        }

        Cow::from(val.0).for_each_shallow(&mut |val: Cow<Val>| {
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

        res
    }

    pub fn call_iter(&mut self, r: &mut LocalVars, val: Val, ispan: Span) -> Val {
        let call_iterate = Val::Tup(vec![Val::str("iter"), val]);
        self.try_call(call_iterate, ispan, r)
            .unwrap_or_else(|v| Val::err(RuntimeError::InvalidIter(Box::new(v)), Some(ispan)))
    }

    pub fn call_next(&mut self, r: &mut LocalVars, val: Val, ispan: Span) -> Val {
        let call_iterate = Val::Tup(vec![Val::str("next"), val]);
        self.try_call(call_iterate, ispan, r)
            .unwrap_or_else(|v| Val::err(RuntimeError::InvalidNext(Box::new(v)), Some(ispan)))
    }

    fn do_for_iter(&mut self, r: &mut LocalVars, pat: &Pat, iter: &ExprS, body: &Vec<ExprS>) -> (Val, Control) {
        let mut res = (Val::void(), Control::Done);
        let ispan = iter.1;
        let (mut cur, con) = self.from_expr(iter, r);
        if con.stops_exec() {
            return (cur, con)
        }
        //let mut cur = self.call_iter(r, val.0, ispan);
        loop {
            {
                if cur.is_err() { return (cur, Control::Done) }
                if cur.len() < 2 { break; }
                let v = cur.get_tup().unwrap();
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
            cur = self.call_next(r, cur, ispan);
            if cur.is_void() { break }
        }
        res
    }

    fn do_string(&mut self, s: &str, _: &mut LocalVars) -> (Val, Control) {
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

    fn do_xstring(&mut self, v: &Vec<ExprS>, r: &mut LocalVars) -> (Val, Control) {
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

    fn do_background(&mut self, e: &ExprS, r: &mut LocalVars) -> (Val, Control) {
        use jobs::SpawnResult::*;

        match self.jobs.spawn_bg() {
            Ok(Original(job)) => {
                (Val::Tup(vec![Val::str("Job"), Val::Str(job.jid().unwrap().to_string()),
                                                Val::Str(job.pid().unwrap().to_string())]),
                     Control::Done)
            }
            Ok(Child) => {
                let ret = self.exec_stmt(e, r);
                let code = ret.0.get_int().unwrap_or(0) as i32;
                ::std::process::exit(code)
            },
            Err(e) => (Val::err_string(format!("{}", e)), Control::Done),
        }
    }

    pub fn from_expr(&mut self, e: &ExprS, r: &mut LocalVars) -> (Val, Control) {
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
            Hereval(ref expr) => {
                let (val, con) = self.from_expr(&**expr, r);
                if con.stops_exec() {
                    return (val, con)
                }
                if let Ok(text) = val.take_str() {
                    (Str(text), Control::Done)
                } else {
                    unimplemented!()
                }
            },
            Block(ref b) => {
                r.enter_scope();
                let res = self.exec_stmt_list(b, r);
                r.exit_scope();
                res
            },
            Lambda(ref c, ref p, ref b) => self.do_lambda(r, c, p, b),
            Var(m, ref n) => (self.get_var_ref(m, n, r), Control::Done),
            Exec(m, ref n, _) => self.get_exec(m, n, r),
            ExecList(m, ref n, _) => self.get_exec_list(m, n, r),
            Call(m, ref n, _) => self.do_call(m, n, r),
            Expr::Range(ref rng) => {
                use rush_parser::ast::ASTRange;
                use rush_parser::ast::ASTRange::*;
                fn eval_expr(i: &mut Interp, e: &ExprS, l: &mut LocalVars) -> Result<ExprS, (Val, Control)> {
                    if let Some(_) = e.0.get_atom() {
                        return Ok(e.clone());
                    }
                    let (val, con) = i.from_expr(e, l);
                    if con.stops_exec() {
                        return Err((val, con));
                    }
                    Ok(ExprS(Expr::String(val.get_string().expect("Sides of range must be scalar")), e.1))
                }
                let rng = match *rng {
                    All => Ok(All),
                    From(ref x) => eval_expr(self, &**x, r).map(|x| From(Box::new(x))),
                    Till(ref x) => eval_expr(self, &**x, r).map(|x| Till(Box::new(x))),
                    Within(ref x, ref y) => {
                        let x = eval_expr(self, &**x, r);
                        match x {
                            Ok(x) => eval_expr(self, &**y, r).map(|y| Within(Box::new(x), Box::new(y))),
                            Err(err) => Err(err),
                        }
                    },
                };
                match rng {
                    Ok(r) => match ASTRange::into_range(r.into()) {
                        Ok(r) => (r.as_val(), Control::Done),
                        Err(x) => (Val::err(RuntimeError::ParseError(x), Some(e.1)), Control::Done),
                    },
                    Err(x) => x,
                }
            },
            Expr::Rex(ref r) => {
                ((&r.0).into(), Control::Done)
            }
            If{ref cond, ref then, ref el} => self.do_if(r, cond, then, el),
            While{ref cond, ref lo} => self.do_while(r, cond, lo),
            Match{ref val, ref cases} => self.do_match(r, val, cases),
            MatchAll{ref val, ref cases} => self.do_match_all(r, val, cases),
            Consume{ref val, ref cases} => self.do_consume(r, val, cases),
            For{ref pat, ref val, ref lo} => self.do_for(r, pat, val, lo),
            ForIter{ref pat, ref iter, ref lo} => self.do_for_iter(r, pat, iter, lo),
            Read(ref ids) => self.do_read(ids, r),
            Recv(ref pat) => self.do_recv(pat, r, false),
            Member(m, ref lhs, ref rhs) => {
                let (lval, con) = self.from_expr(&**lhs, r);
                if con.stops_exec() {
                    return (lval, con);
                }
                if lval.is_err() {
                    return (lval, Control::Done);
                }
                let (mut rval, con) = self.from_expr(&**rhs, r);
                if con.stops_exec() {
                    return (rval, con);
                }
                rval.eval();
                let to_call = match rval {
                    e @ Val::Error(..) => return (e, Control::Done),
                    Val::Str(s) => vec![Val::Str("op::get_prop".into()), lval, Val::Str(s)],
                    Val::Tup(mut v) => { v.insert(1, lval); v },
                    _ => unreachable!(),
                };
                let val = self.call(Val::Tup(to_call), e.1, r);
                (val.subst(m), Control::Done)
            },
            Index(m, ref val, ref index) => {
                let (val, con) = self.from_expr(&**val, r);
                if con.stops_exec() {
                    return (val, con);
                }
                if val.is_err() {
                    return (val, Control::Done);
                }
                let (mut index, con) = self.from_expr(&**index, r);
                if con.stops_exec() {
                    return (index, con);
                }
                index.eval();
                if index.is_err() {
                    return (index, Control::Done)
                }
                let to_call = vec![Val::Str("op::index".into()), val, index];
                let val = self.call(Val::Tup(to_call), e.1, r);
                (val.subst(m), Control::Done)
            },
            _ => unimplemented!(),
        }
    }

    fn do_call(&mut self, m: SubsMode, n: &ExprS, l: &mut LocalVars) -> (Val, Control) {
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
        (val.subst(m), con)
    }

    fn get_exec(&mut self, _: SubsMode, n: &ExprS, l: &mut LocalVars) -> (Val, Control) {
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

    fn get_exec_list(&mut self, m: SubsMode, n: &ExprS, l: &mut LocalVars) -> (Val, Control) {
        let (val, con) = self.get_exec(m, n, l);
        if con.stops_exec() {
            return (val, con);
        }
        if let Val::Str(str) = val {
            let mut ret = vec![];
            for line in str.lines() {
                ret.push(Val::Tup(line.split_whitespace().map(|x| Val::str(x)).collect()))
            }
            (Val::Tup(ret).subst(m), Control::Done)
        } else {
            (Val::void(), Control::Done)
        }
    }

    fn get_var_ref(&mut self, m: SubsMode, n: &ExprS, r: &mut LocalVars) -> Val {
        use self::Expr::*;
        match n.0 {
            Ident(ref id) => self.get_var_ref_id(m, id, n.1, r),
            Var(_, ref e) => {
                let var = self.get_var_ref(SubsMode::new(), e, r);
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

    fn get_var_ref_id(&mut self, m: SubsMode, id: &str, span: Span, r: &mut LocalVars) -> Val {
        let v = r.get(id);
        let r = match v {
            Some(r) => Val::Ref(r.clone()),
            None => return Val::err(RuntimeError::UnboundVariable(id.into()), Some(span)),
        };
        //println!("var: {:?}", r);
        r.subst(m)
    }

    pub fn try_call(&mut self, val: Val, span: Span, l: &mut LocalVars) -> Result<Val, Val> {
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

    pub fn call(&mut self, val: Val, span: Span, l: &mut LocalVars) -> Val {
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

    pub fn do_set(&mut self, op: SetOp, n: &ExprS, mut val: Val, local_vars: &mut LocalVars) -> Val {
        fn imp(this: &mut Interp, n: &ExprS, l: &mut LocalVars, f: &mut FnMut(&mut Interp, &mut Val)) -> Result<(), Val> {
            fn do_id(this: &mut Interp, id: &str, l: &mut LocalVars, f: &mut FnMut(&mut Interp, &mut Val)) -> Result<(), Val> {
                if let Some(var) = l.get(id) {
                    var.with_mut(|x| f(this, x));
                    return Ok(());
                }
                let var = l.bind(id.clone(), Val::void());
                var.with_mut(|x| f(this, x));
                Ok(())
            }

            match n.0 {
                Expr::Ident(ref id) => {
                    do_id(this, id, l, f)
                },
                Expr::Index(_, ref lhs, ref index) => {
                    use rush_rt::val::Indexing;
                    let (index, con) = this.from_expr(&*index, l);
                    return index.with_val(move |index| {
                        if con.stops_exec() {
                            return Ok(());
                        }
                        match Indexing::from_val(&index) {
                            Ok(index) => {
                                imp(this, lhs, l, &mut |this: &mut Interp, v: &mut Val| {
                                    v.with_index_mut(&index, &mut |v: &mut Val| {
                                        v.simplify_shallow();
                                        f(this, v);
                                    }).unwrap();
                                })
                            },
                            Err(err) => return Err(err),
                        }
                    })
                },
                Expr::Member(..) => {
                    Err(Val::err_str("Indexed setting to properties not suppported"))
                },
                Expr::Tuple(..) => {
                    Err(Val::err_str("Setting to tuples not suppported"))
                },
                _ => {
                    let (val, con) = this.from_expr(n, l);
                    if con.stops_exec() {
                        return Ok(())
                    }
                    match val.take_str() {
                        Ok(ref id) if ::rush_parser::lex::is_identifier(id) => {
                            do_id(this, id, l, f)
                        },
                        Ok(id) => {
                            Err(Val::err_string(format!("Invalid identifier: {:?}", id)))
                        },
                        Err(val) => {
                            Err(Val::err_string(format!("Invalid identifier: {:?}", val)))
                        },
                    }
                }
            }
        }

        match n.0 {
            Expr::Member(_, ref lhs, ref rhs) => {
                if op != SetOp::Assign {
                    return Val::err_str("Must use ordinary assignment when setting properties")
                }
                let (mut rval, con) = self.from_expr(&**rhs, local_vars);
                if con.stops_exec() {
                    return rval;
                }
                rval.eval();
                let mut to_call = match rval {
                    e @ Val::Error(..) => return e,
                    Val::Str(_) => rval,
                    Val::Tup(_) => return Val::err_str("Cannot set into method calls, only properties"),
                    _ => unreachable!(),
                };
                let lspan = lhs.1;
                match imp(self, lhs, local_vars, &mut |this: &mut Interp, old_val: &mut Val| {
                    let mut tmp = Val::void();
                    ::std::mem::swap(&mut tmp, old_val);
                    let mut input = Val::void();
                    ::std::mem::swap(&mut val, &mut input);
                    let mut prop_name = Val::void();
                    ::std::mem::swap(&mut to_call, &mut prop_name);
                    let call = vec!["op::set_prop".into(), tmp, prop_name, input];
                    match this.try_call(Val::Tup(call), lspan, &mut LocalVars::new()) {
                        Ok(mut val) => {
                            ::std::mem::swap(old_val, &mut val);
                        },
                        Err(val) => {
                            //eprintln!("val: {:?}", val);
                            let mut iter = val.take_tup().unwrap().into_iter();
                            iter.next().unwrap(); // Discard fn name
                            let mut val = iter.next().unwrap();
                            let prop = iter.next().unwrap();
                            let mut input = iter.next().unwrap();

                            use ::rush_rt::val::Indexing;
                            let index = Indexing::from_val(&prop);
                            if let Ok(index) = index {
                                match val.with_index_mut(&index, &mut |old_val: &mut Val| {
                                    ::std::mem::swap(old_val, &mut input);
                                }) {
                                    Ok(..) => ::std::mem::swap(old_val, &mut val),
                                    Err(..) => {},
                                }
                            }
                        },
                    }
                }) {
                    Ok(..) => Val::void(),
                    Err(e) => e,
                }
            },
            _ => {
                match imp(self, n, local_vars, &mut |_this: &mut Interp, old_val: &mut Val| {
                    use self::SetOp::*;
                    match op {
                        Assign => {
                            ::std::mem::swap(old_val, &mut val);
                        },
                        AssignIfNull => if old_val.is_void() {
                            ::std::mem::swap(old_val, &mut val);
                        },
                        Suffix => match old_val {
                            &mut Val::Tup(ref mut v) => {
                                let mut tmp = Val::void();
                                ::std::mem::swap(&mut tmp, &mut val);
                                v.push(tmp);
                            },
                            _ => {
                                let mut tmp = Val::void();
                                ::std::mem::swap(&mut tmp, old_val);
                                let mut new = Val::void();
                                ::std::mem::swap(&mut new, &mut val);
                                *old_val = Val::Tup(vec![tmp, new]);
                            },
                        },
                        Prefix => match old_val {
                            &mut Val::Tup(ref mut v) => {
                                let mut tmp = Val::void();
                                ::std::mem::swap(&mut tmp, &mut val);
                                v.insert(0, tmp);
                            },
                            _ => {
                                let mut tmp = Val::void();
                                ::std::mem::swap(&mut tmp, old_val);
                                let mut new = Val::void();
                                ::std::mem::swap(&mut new, &mut val);
                                *old_val = Val::Tup(vec![new, tmp]);
                            },
                        },
                    }
                }) {
                    Ok(..) => Val::void(),
                    Err(e) => e,
                }
            },
        }
    }

    pub fn exec_stmt(&mut self, stmt_s: &ExprS, local_vars: &mut LocalVars) -> (Val, Control) {
        self.jobs.poll();

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
                (self.do_set(op, &**n, val.0, local_vars), Control::Done)
            },
            Expr::Import(scope, ref name, ref options, ref rename, ref assign) => {
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
                    let options = options.clone().map(|x| self.from_expr(&*x, local_vars).0 );
                    let var = self.lookup_import(scope, name, options);
                    if let Some((op, val)) = assign {
                        match op {
                            SetOp::Assign => var.set(val),
                            SetOp::AssignIfNull => {
                                if var.get().is_void() {
                                    var.set(val)
                                }
                            },
                            _ => unimplemented!(),
                        }
                    }
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
            Expr::Tuple(..) | Expr::Ident(..) | Expr::String(..) | Expr::XString(..) | Expr::Range(..) |
                Expr::LString(..) | Expr::Exec(..) | Expr::ExecList(..) | Expr::Call(..) | Expr::Var(..) | Expr::Lambda(..) |
                Expr::Rex(..) | Expr::Hereval{..} => {
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
            Expr::If{..} | Expr::While{..} |
                Expr::Match{..} | Expr::MatchAll{..} | Expr::Consume{..} |
                Expr::For{..} | Expr::ForIter{..} | Expr::Block(..) |
                Expr::Read(..) | Expr::Recv(..) |
                Expr::Member(..) | Expr::Index(..) => {
                self.from_expr(stmt_s, local_vars)
            },
            Expr::Background(ref expr) => {
                self.do_background(&*expr, local_vars)
            },
            Expr::Pipe(ref stages) => {
                self.do_pipe(stages, local_vars)
            },
            Expr::And(ref lhs, ref rhs) => {
                self.do_and_or(&*lhs, &*rhs, false, local_vars)
            },
            Expr::Or(ref lhs, ref rhs) => {
                self.do_and_or(&*lhs, &*rhs, true, local_vars)
            },
            Expr::Manip(ref ops, ref expr) => {
                fn apply(interp: &mut Interp, ops: &[ManOp], expr: &ExprS, local_vars: &mut LocalVars) -> (Val, Control) {
                    if ops.len() == 0 {
                        interp.exec_stmt(expr, local_vars)
                    } else {
                        match ops[0] {
                            ManOp::Merge{from, into} => {
                                eprintln!("Redirect fd {} to fd {}", from, into);
                                let _guard = if from != into { Some(IOGuard::redir(from, into)) } else { None };
                                apply(interp, &ops[1..], expr, local_vars)
                            },
                            ManOp::Output{fd, ref sink} => {
                                let (val, con) = interp.from_expr(&**sink, local_vars);
                                if con.stops_exec() {
                                    return (val, con)
                                }
                                if let Some(fname) = val.get_str() {
                                    use std::fs::File;
                                    use std::os::unix::io::IntoRawFd;

                                    let fout = File::create(fname.to_string()).unwrap();
                                    let fdout = fout.into_raw_fd();

                                    eprintln!("Redirect fd {} into file {:?} at fd {}", fd, fname, fdout);
                                    let _guard = IOGuard::redir(fd, fdout);
                                    apply(interp, &ops[1..], expr, local_vars)
                                } else {
                                    unimplemented!()
                                }
                            },
                            ManOp::Input{fd, ref source} => {
                                let (val, con) = interp.from_expr(&**source, local_vars);
                                if con.stops_exec() {
                                    return (val, con)
                                }
                                if let Some(fname) = val.get_str() {
                                    use std::fs::File;
                                    use std::os::unix::io::IntoRawFd;

                                    let fin = File::open(fname.to_string()).unwrap();
                                    let fdin = fin.into_raw_fd();

                                    eprintln!("Redirect fd {} from file {:?} at fd {}", fd, fname, fdin);
                                    let _guard = IOGuard::redir(fd, fdin);
                                    apply(interp, &ops[1..], expr, local_vars)
                                } else {
                                    unimplemented!()
                                }
                            },
                            ManOp::Heredoc{expr: ref e} => {
                                let (val, con) = interp.from_expr(&**e, local_vars);
                                if con.stops_exec() {
                                    return (val, con)
                                }
                                if let Ok(text) = val.take_str() {
                                    use std::io::{Write, Seek, SeekFrom};
                                    use std::os::unix::io::IntoRawFd;

                                    let mut tmpf = ::tempfile::tempfile().unwrap();

                                    tmpf.write_all(text.as_bytes()).unwrap();
                                    tmpf.seek(SeekFrom::Start(0)).unwrap();

                                    let fdhere = tmpf.into_raw_fd();
                                    let _guard = IOGuard::redir(0, fdhere);
                                    apply(interp, &ops[1..], expr, local_vars)
                                } else {
                                    unimplemented!()
                                }
                            },
                        }
                    }
                }
                apply(self, &ops[..], expr, local_vars)
            },
        }
    }

    fn do_and_or(&mut self, lhs: &ExprS, rhs: &ExprS, is_or: bool, local_vars: &mut LocalVars) -> (Val, Control) {
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

    fn do_pipe(&mut self, stages: &Vec<ExprS>, local_vars: &mut LocalVars) -> (Val, Control) {
        let mut pipeline = Pipeline::create(stages);
        let (val, con) = pipeline.exec(self, local_vars);
        (val, con)
    }

    fn do_read(&mut self, ids: &Vec<ExprS>, local_vars: &mut LocalVars) -> (Val, Control) {

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

    fn do_recv(&mut self, pat: &Pat, local_vars: &mut LocalVars, exact: bool) -> (Val, Control) {
        use std::io::{self, BufRead};

        let stdin = io::stdin();
        let ret = match stdin.lock().lines().next() {
            Some(line) => match line {
                Ok(line) => {
                    use builtins::mkval_str;
                    let val = mkval_str(self, local_vars, &line);
                    if exact {
                        if pat.subsumes(&val) == Subsumption::Contains {
                            pat.do_match_unchecked(val.into(), local_vars);
                            (Val::true_(), Control::Done)
                        } else {
                            (Val::false_(), Control::Done)
                        }
                    } else {
                        pat.do_match_unchecked(val.into(), local_vars);
                        (Val::true_(), Control::Done)
                    }
                },
                Err(err) => {
                    (Val::err_string(format!("{:?}", err)), Control::Done)
                },
            },
            None => (Val::false_(), Control::Done),
        };
        return ret;
    }

    pub fn exec_stmt_list(&mut self, stmt_list: &Vec<ExprS>, local_vars: &mut LocalVars) -> (Val, Control) {
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

    pub fn exec(&mut self, stmt_list: &Vec<ExprS>) -> (Val, Control) {
        let mut local_vars = LocalVars::new();
        local_vars.enter_scope();
        let ret = self.exec_stmt_list(stmt_list, &mut local_vars);
        ret.0.unhandled();
        local_vars.exit_scope();
        ret
    }
}

pub struct IOGuard {
    from: i32,
    old: i32,
}

impl IOGuard {
    pub fn redir(from: i32, into: i32) -> Self {
        use nix::fcntl::{self, fcntl, FcntlArg};

        let old = dup(from).unwrap();
        fcntl(old, FcntlArg::F_SETFL(fcntl::O_CLOEXEC)).unwrap();
        close(from).unwrap();
        dup2(into, from).unwrap();
        IOGuard{from, old}
    }
}

impl Drop for IOGuard {
    fn drop(&mut self) {
        close(self.from).unwrap();
        dup2(self.old, self.from).unwrap();
        close(self.old).unwrap();
    }
}
