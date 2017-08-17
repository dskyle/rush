//#![feature(plugin)]
//#![plugin(plex)]
#![feature(inclusive_range_syntax)]
#![feature(box_patterns)]
#![feature(splice)]
#![feature(slice_get_slice)]

//extern crate regex;

#[macro_use]
extern crate lazy_static;

extern crate rush_parser;

#[macro_use]
extern crate rush_pat;

extern crate rush_rt;

extern crate users;

extern crate nix;

extern crate tempfile;

extern crate glob;


pub mod func;
pub mod interp;

use rush_pat::pat::Pat;
use func::{Func};
pub use rush_rt::val::Val;
pub use func::Control;
use rush_rt::val::InternalIterable;
use std::borrow::Cow;

pub mod util {
    use rush_pat::range::Range;
    use rush_rt::range::RangeExt;
    use std::process::Command;
    use rush_rt::val::{Val, ValIterOps, InternalIterable};
    use rush_rt::error::RuntimeError;
    use self::Val::*;
    use std::borrow::{Cow};
    use interp::Jobs;

    pub fn add(val: &Val) -> i64 {
        let mut acc = 0;
        Cow::from(val).for_each(&mut |s: Cow<str>, _| { acc += str::parse::<i64>(&*s).unwrap_or(0); return true } );
        acc
    }

    pub fn echo(val: &Val) {
        let mut count = 0;
        Cow::from(val).for_each(&mut |s: Cow<str>, _| {
            if count > 0 { print!(" "); }
            print!("{}", &*s);
            count += 1;
            return true
        });
        println!("");
    }

    pub fn repr(val: &Val) {
        let mut val = val.clone();
        val.eval();
        if val.len() == 1 {
            println!("{}", val.iter().next().unwrap());
        } else {
            println!("{}", val);
        }
    }

    pub fn debug(val: &Val) {
        if val.len() == 1 {
            println!("{:?}", val.iter().next().unwrap());
        } else {
            println!("{:?}", val);
        }
    }

    pub fn list_dict_keys(val: &Val) -> Vec<String> {
        let mut ret = vec![];
        Cow::from(val).for_each_shallow(&mut |val: Cow<Val>| {
            match *(val.as_ref()) {
                Tup(ref v) if v.len() == 2 => {
                    if let Some(key) = v[0].get_string() {
                        ret.push(key);
                    }
                },
                _ => {},
            }
            return true;
        });
        ret
    }

    pub fn list_dict_values(val: &Val) -> Vec<Val> {
        let mut ret = vec![];
        Cow::from(val).for_each_shallow(&mut |val: Cow<Val>| {
            match *(val.as_ref()) {
                Tup(ref v) if v.len() == 2 => {
                    if let Val::Str(_) = v[0] {
                        ret.push(v[1].clone());
                    }
                },
                _ => {},
            }
            return true;
        });
        ret
    }

    fn wrap_index(i: i64, len: usize) -> usize {
        if i < 0 {
            len - (-i as usize)
        } else {
            i as usize
        }
    }

    pub fn index_str(val: &Val, i: &str) -> Val {
        let mut ret = None;
        Cow::from(val).for_each_shallow(&mut |val: Cow<Val>| {
            match *(val.as_ref()) {
                Tup(ref v) if v.len() == 2 && v[0].get_string().map_or(false, |x| x == i) => {
                    ret = Some(v[1].clone()); return false
                },
                _ => {},
            }
            return true;
        });
        ret.unwrap_or_else(||
            Val::err(RuntimeError::KeyNotFound{keys: list_dict_keys(val), idx: i.into()}, None))
    }

    pub fn index_int(val: &Val, idx: i64) -> Val {
        match val {
            &Ref(ref r) => return index_int(&*r.get_ref(), idx),
            &Tup(ref v) => {
                let i = wrap_index(idx, v.len());
                if i >= v.len() {
                    return Val::err(RuntimeError::IndexOutOfRange{len: v.len(), idx}, None);
                }
                let ret = &v[i];
                return ret.clone();
            },
            &Error(ref e) => {
                e.1.set(true);
                let i = wrap_index(idx, e.0.len() + 1);
                if i == 0 { return Val::str("Err!"); }
                if i - 1 < e.0.len() {
                    let ret = &e.0[i - 1];
                    return ret.clone();
                }
                return Val::err(RuntimeError::IndexOutOfRange{len: e.0.len() + 1, idx}, None);
            }
            _ => if idx == 0 || idx == -1 { return val.clone(); } else {
                return Val::err(RuntimeError::IndexOutOfRange{len: 1, idx}, None);
            },
        }
    }

    use std::slice::SliceIndex;

    fn index_slice<S: SliceIndex<[Val], Output = [Val]> + ::std::fmt::Debug>(val: &Val, s: S) -> Val {
        match val {
            &Tup(ref v) => {
                match v.get(s) {
                    Some(v) => Val::Tup(v.iter().cloned().collect()),
                    None => Val::err_str("Bad index slice"),
                }
            },
            _ => Val::err_str("Bad index slice"),
        }
    }

    pub fn index_range(val: &Val, r: Range) -> Val {
        match *val {
            Ref(ref rf) => return index_range(&*rf.get_ref(), r),
            Error(ref e) => {
                let mut v = Vec::with_capacity(1 + e.0.len());
                v.push(Val::str("Err!"));
                v.extend_from_slice(&e.0[..]);
                return index_range(&Tup(v), r);
            },
            Tup(ref v) => {
                match r {
                    Range::All => return val.clone(),
                    Range::FromInt(l) => index_slice(val, wrap_index(l, v.len())..),
                    Range::TillInt(r) => index_slice(val, ...wrap_index(r, v.len())),
                    Range::WithinInt(l, r) => index_slice(val, wrap_index(l, v.len())...wrap_index(r, v.len())),
                    _ => Val::err(RuntimeError::InvalidIndex(Box::new(r.as_val()), "Index must be a scalar or non-negative integer range"), None)
                }
            },
            _ => unimplemented!(),
        }
    }

    use interp::Indexing;

    pub fn index(val: &Val, i: Indexing) -> Val {
        use self::Indexing::*;
        match i {
            NoIndex => unreachable!(),
            Offset(o) => index_int(val, o),
            Dict(k) => index_str(val, k),
            Indexing::Range(r) => index_range(val, r),
        }
    }

    pub fn system(val: &Val) -> Val {
        use ::std::iter::IntoIterator;

        let cmd = val.iter().flatten();
        let mut iter = cmd.take_tup().unwrap().into_iter().map(|x| x.take_str().unwrap());
        let status = Command::new(iter.next().expect("system requires at least one argument")).args(iter).status();
        match status {
            Ok(status) => {
                match status.code() {
                    Some(i) => Tup(vec![Str("Status".into()), Str(i.to_string())]),
                    None => Tup(vec![Str("Killed".into()), Str("Unknown".into())]),
                }
            },
            Err(error) => {
                Val::err_string(format!("{}",error))
            },
        }
    }

    pub fn equals(l: &Val, r: &Val) -> Val {
        //println!("equals: {:?}  {:?}", l, r);
        let eq = Cow::from(l).for_each_pairs(r, &mut |l: Option<Cow<str>>, r: Option<&str>, _| {
            //println!("{}: {:?} ?= {:?}", d, l, r);
            match (l, r) {
                (Some(l), Some(r)) => { return l.as_ref() == r; },
                _ => return false,
            }
        });
        if eq {
            Val::true_()
        } else {
            Val::false_()
        }
    }

    pub fn range_iter_start(l: &Val, r: &Val) -> Val {
        let range = Range::from_val_pair(l, r).unwrap();
        Val::Tup(vec![Val::str("Range::Iter"), range.first().unwrap(), l.clone(), r.clone()])
    }

    pub fn range_iter_next(cur: &Val, l: &Val, r: &Val) -> Val {
        let range = Range::from_val_pair(l, r).unwrap();
        let next = range.next(cur).unwrap();
        let len = { next.get_tup().map(|x| x.len()).unwrap_or(1) };
        if len == 0 {
            Val::void()
        } else {
            Val::Tup(vec![Val::str("Range::Iter"), next, l.clone(), r.clone()])
        }
    }

    pub fn get_home() -> String {
        use std::env::var;
        let home = var("HOME").unwrap_or_else(|_| {
            use users::{get_user_by_uid, get_current_uid};
            let user = get_user_by_uid(get_current_uid()).unwrap();
            let username = user.name();

            "/home/".to_string() + username
        });
        home
    }

    pub fn cd(mut dir: Cow<str>) -> Val {
        use std::env::{current_dir, set_current_dir};
        use std::path::{PathBuf};
        use std::sync::Mutex;
        use std::ops::{Deref, DerefMut};

        lazy_static! {
                static ref LAST_DIR: Mutex<String> = Mutex::new(get_home());
        }

        let old_dir = current_dir().unwrap_or_else(|_| { PathBuf::from("/") });
        if dir == "~" || dir.starts_with("~/") {
            dir = Cow::Owned(get_home() + &dir[1..]);
        }
        if dir == "-" {
            dir = Cow::Owned(LAST_DIR.lock().unwrap().deref().clone());
        }
        let mut new_dir = old_dir.clone();
        new_dir.push(dir.as_ref());
        if let Err(err) = set_current_dir(new_dir) {
            Val::err_string(format!("{}", err))
        } else {
            {
                *LAST_DIR.lock().unwrap().deref_mut() = old_dir.to_string_lossy().to_owned().into();
            }
            Val::void()
        }
    }

    pub fn jobs(j: &Jobs) -> Val {
        let jobs = j.iter().map(|(id, pid)| {
            Val::Tup(vec![Val::str("Job"),
                          Val::Str(id.to_string()),
                          Val::Str(pid.to_string())]) }).collect();
        Val::Tup(jobs)
    }

    pub fn file2string(fname: &str) -> String {
        use std::fs::File;
        use std::io::BufReader;
        use std::io::Read;

        let file = File::open(fname).unwrap();
        let mut buf_reader = BufReader::new(file);
        let mut contents = String::new();
        buf_reader.read_to_string(&mut contents).unwrap();
        contents
    }
}

mod builtins {
    use rush_pat::range::{Range};
    use rush_rt::vars::{LocalVars, Resolver};
    use rush_rt::val::{Val, ValIterOps};
    use rush_rt::range::RangeExt;
    use interp::{Interp};
    use util;
    use self::Val::*;
    use std::borrow::Cow;

    pub fn echo(_: &Interp, locs: &mut LocalVars) -> Val
    {
        let arg = locs.get("args").unwrap();
        util::echo(&*arg.get_ref());
        Val::status(0)
    }

    pub fn repr(_: &Interp, locs: &mut LocalVars) -> Val
    {
        let arg = locs.get("args").unwrap();
        util::repr(&*arg.get_ref());
        Val::status(0)
    }

    pub fn debug(_: &Interp, locs: &mut LocalVars) -> Val
    {
        let arg = locs.get("args").unwrap();
        util::debug(&*arg.get_ref());
        Val::status(0)
    }

    pub fn add(_: &Interp, locs: &mut LocalVars) -> Val
    {
        let args = locs.get("args").unwrap().get_ref();
        let ret = util::add(&*args);
        Val::Str(ret.to_string())
    }

    pub fn expand_range(_: &Interp, locs: &mut LocalVars) -> Val
    {
        let args = locs.get("range").unwrap().get_ref();
        Range::from_val(&*args)
            .and_then(|x| x.enumerate())
            .unwrap_or_else(|x| Val::err(x, None))
    }

    pub fn val(_: &Interp, locs: &mut LocalVars) -> Val
    {
        let mut args = locs.get("args").unwrap().get();
        args.eval();
        if let Tup(..) = args {
            if args.len() == 1 {
                if let Tup(v) = args {
                    return v.into_iter().next().unwrap()
                } else { unreachable!() }
            }
        }
        args
    }

    use interp::Indexing;

    pub fn index(_: &Interp, locs: &mut LocalVars) -> Val
    {
        let tup = locs.get("tup").unwrap().get();
        let i = locs.get("i").unwrap().get();
        match Indexing::from_val(&i) {
            Ok(index) => util::index(&tup, index),
            Err(err) => return err,
        }
        /*
        if let Some(i) = i.get_str() {
            if let Ok(i) = str::parse::<usize>(i) {
                util::index_usize(&tup, i)
            } else {
                util::index_str(&tup, i)
                //use rush_rt::val::IntoVal;
                //Val::err(RuntimeError::InvalidIndex(i.into_val().into(), "Index must be a positive integer"), None)
            }
        } else if let Ok(rng) = Range::from_val(&i) {
            util::index_range(&tup, rng)
        } else {
            Val::err(RuntimeError::InvalidIndex(i.clone().into(), "Index must be a scalar or range"), None)
        }*/
    }

    pub fn system(_: &Interp, locs: &mut LocalVars) -> Val
    {
        let arg = locs.get("args").unwrap();
        let val = util::system(&*arg.get_ref());
        val
    }

    pub fn equals(_: &Interp, locs: &mut LocalVars) -> Val
    {
        let l = locs.get("l").unwrap();
        let r = locs.get("r").unwrap();
        let val = util::equals(&*l.get_ref(), &*r.get_ref());
        val
    }

    pub fn eval(i: &Interp, locs: &mut LocalVars, args: Val) -> Val
    {
        let cmd = args.iter().flatten().iter().join(" ");
        let mut lex = ::rush_parser::lex::ContextLexer::new();
        let parsed = ::rush_parser::parse::parse(lex.lex(cmd.as_ref()));
        let (v, _) = i.exec_stmt_list(&mut parsed.unwrap(), locs);
        v
    }

    pub fn source(i: &Interp, locs: &mut LocalVars, args: Val) -> Val
    {
        let contents = util::file2string(args.get_str().expect("source takes one argument: file name"));
        let mut lex = ::rush_parser::lex::ContextLexer::new();
        let parsed = ::rush_parser::parse::parse(lex.lex(&contents));
        let (v, _) = i.exec_stmt_list(&mut parsed.unwrap(), locs);
        v
    }

    fn get_tup_dict(args: &Val) -> &Val {
        match *args {
            Val::Tup(ref v) => {
                //println!("v: {:?}", v);
                if v.len() == 1 {
                    if let Val::Tup(ref w) = v[0] {
                        //println!("w: {:?}", w);
                        if w.len() == 2 && w[0].get_str().is_some() {
                            // fall through
                        } else {
                            return &v[0];
                        }
                    }
                }
            },
            _ => unreachable!(),
        }
        return args
    }

    pub fn keys(_: &Interp, locs: &mut LocalVars) -> Val
    {
        let args = locs.get("args").unwrap().get_ref();
        //println!("args: {:?}", args);
        let ret = util::list_dict_keys(get_tup_dict(&*args));
        ret.into()
    }

    pub fn values(_: &Interp, locs: &mut LocalVars) -> Val
    {
        let args = locs.get("args").unwrap().get_ref();
        //println!("args: {:?}", args);
        let ret = util::list_dict_values(get_tup_dict(&*args));
        ret.into()
    }

    pub fn range_iter_start(_: &Interp, locs: &mut LocalVars) -> Val
    {
        let l = locs.get("l").unwrap();
        let r = locs.get("r").unwrap();
        let val = util::range_iter_start(&*l.get_ref(), &*r.get_ref());
        val
    }

    pub fn range_iter_next(_: &Interp, locs: &mut LocalVars) -> Val
    {
        let cur = locs.get("cur").unwrap();
        let l = locs.get("l").unwrap();
        let r = locs.get("r").unwrap();
        let val = util::range_iter_next(&*cur.get_ref(), &*l.get_ref(), &*r.get_ref());
        val
    }

    pub fn cd(_: &Interp, locs: &mut LocalVars) -> Val
    {
        let dir = locs.get("args");
        let dir = if let Some(x) = dir {
            x.get().get_string().map(|x| { Cow::Owned(x) } )
        } else {
            Some(Cow::Borrowed("~"))
        };
        let dir = dir.unwrap_or(Cow::Borrowed("~"));
        util::cd(dir)
    }

    pub fn jobs(i: &Interp, _: &mut LocalVars) -> Val
    {
        util::jobs(&i.jobs.borrow())
    }

    pub fn op_bool_status(_: &Interp, locs: &mut LocalVars) -> Val
    {
        let s = locs.get("s").unwrap();
        if s.get_ref().get_str() == Some("0") {
            Val::str("1")
        } else {
            Val::str("0")
        }
    }

    pub fn exit(_: &Interp, locs: &mut LocalVars) -> Val
    {
        let status = locs.get("args");
        let status = if let Some(x) = status {
            x.get().get_str().and_then(|x| str::parse::<i32>(x).ok()).unwrap_or(0)
        } else {
            0
        };
        ::std::process::exit(status)
    }

}

pub fn test(input: &str) -> () {
    {
        let mut lex = rush_parser::lex::ContextLexer::new();
        for cur in lex.lex(input) {
            println!("{:?}", cur)
        }
    }
    {
        let mut lex = rush_parser::lex::ContextLexer::new();
        let parsed = rush_parser::parse::parse(lex.lex(input));
        println!("{:#?}", parsed);
    }
}

fn mk_wild_pat(name: &str) -> Pat {
    use self::Pat::*;

    Tup(vec![Str(name.into()), Wild(vec![ID("args".into())])])
}

fn mk_noarg_pat(name: &str) -> Pat{
    use self::Pat::*;
    Tup(vec![Str(name.into())])
}

fn mk_binary_pat(name: &str) -> Pat{
    use self::Pat::*;
    Tup(vec![Str(name.into()), ID("l".into()), ID("r".into())])
}

use rush_rt::vars::{LocalVars, Scoped};

pub struct Processor {
    interp: interp::Interp,
    locals: LocalVars,
}

impl Processor {
    pub fn new() -> Processor {
        let interp = interp::Interp::new();

        {
            let mut fns = interp.funcs.borrow_mut();
            fns.reg(Func::built_in(mk_wild_pat("system"), builtins::system));
            fns.reg(Func::mac("eval", builtins::eval));
            fns.reg(Func::mac("source", builtins::source));
            fns.reg(Func::built_in(mk_wild_pat("echo"), builtins::echo));
            fns.reg(Func::built_in(mk_wild_pat("repr"), builtins::repr));
            fns.reg(Func::built_in(mk_wild_pat("debug"), builtins::debug));
            fns.reg(Func::built_in(mk_wild_pat("add"), builtins::add));
            fns.reg(Func::built_in(mk_wild_pat("keys"), builtins::keys));
            fns.reg(Func::built_in(mk_wild_pat("values"), builtins::values));
            fns.reg(Func::built_in(mk_pat!( ("expand", {range = ("Range", ...)}) ), builtins::expand_range));
            fns.reg(Func::built_in(mk_wild_pat("val"), builtins::val));
            fns.reg(Func::built_in(mk_pat!( ("op::index", {tup}, {i}) ), builtins::index));
            fns.reg(Func::built_in(mk_binary_pat("equals"), builtins::equals));
            fns.reg(Func::built_in(mk_wild_pat("cd"), builtins::cd));
            fns.reg(Func::built_in(mk_noarg_pat("jobs"), builtins::jobs));
            fns.reg(Func::built_in(mk_wild_pat("exit"), builtins::exit));

            fns.reg(Func::built_in(mk_pat!( ("iter", ("Range", {l}, {r})) ), builtins::range_iter_start));
            fns.reg(Func::built_in(mk_pat!( ("next", ("Range::Iter", {cur}, {l}, {r})) ), builtins::range_iter_next));

            fns.reg(Func::built_in(mk_pat!( ("op::bool", ("Status", {s})) ), builtins::op_bool_status));
        }

        let mut locals = LocalVars::new();
        locals.enter_scope();

        Processor { interp, locals }
    }

    pub fn exec(&mut self, input: &str) -> (Val, Control) {
        let mut lexer = rush_parser::lex::ContextLexer::new();
        let parsed = rush_parser::parse::parse(lexer.lex(input));

        let ret = self.interp.exec_stmt_list(&mut parsed.unwrap(), &mut self.locals);
        ret.0.unhandled();
        ret
    }

    pub fn add_local(&mut self, varname: &str, val: Val) {
        use rush_rt::vars::Binder;

        self.locals.bind(varname, val);
    }
}

pub fn exec(input: &str) -> () {
    test(input);
    let mut prc = Processor::new();
    let (val, _) = prc.exec(input);
    val.unhandled();
    println!("Prog returns: {:?}", val);
    Cow::from(val).for_each(&mut |v: Cow<str>, s| { println!("{}: {:?}", s, v); true } );
}
