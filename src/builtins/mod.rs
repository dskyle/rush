use rush_pat::range::{Range};
use rush_rt::vars::{LocalVars, Resolver};
use rush_rt::val::{Val, ValIterOps, InternalIterable};
use rush_rt::range::RangeExt;
use interp::{Interp};
use util;
use self::Val::*;
use std::borrow::{Borrow, Cow};

pub fn echo(_: &mut Interp, locs: &mut LocalVars) -> Val
{
    let arg = locs.get("args").unwrap();
    util::echo(&arg.get());
    Val::status(0)
}

pub fn repr(_: &mut Interp, locs: &mut LocalVars) -> Val
{
    let arg = locs.get("args").unwrap();
    Val::str(util::repr(&arg.get()))
}

pub fn len(_: &mut Interp, locs: &mut LocalVars) -> Val
{
    let arg = locs.get("args").unwrap();
    Val::str(util::len(&arg.get()))
}

pub fn count(_: &mut Interp, locs: &mut LocalVars) -> Val
{
    let arg = locs.get("args").unwrap();
    Val::str(util::count(&arg.get()))
}

pub fn erepr(_: &mut Interp, locs: &mut LocalVars) -> Val
{
    let arg = locs.get("args").unwrap();
    println!("{}", util::repr(&arg.get()));
    Val::status(0)
}

pub fn debug(_: &mut Interp, locs: &mut LocalVars) -> Val
{
    let arg = locs.get("args").unwrap();
    util::debug(&arg.get());
    Val::status(0)
}

pub fn add(_: &mut Interp, locs: &mut LocalVars) -> Val
{
    let args = locs.get("args").unwrap().get();
    let ret = util::add(&args);
    Val::Str(ret.to_string())
}

pub fn expand_range(_: &mut Interp, locs: &mut LocalVars) -> Val
{
    let args = locs.get("range").unwrap().get();
    Range::from_val(&args)
        .and_then(|x| x.enumerate())
        .unwrap_or_else(|x| Val::err(x, None))
}

pub fn val(_: &mut Interp, locs: &mut LocalVars) -> Val
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

pub fn index(_: &mut Interp, locs: &mut LocalVars) -> Val
{
    let tup = locs.get("tup").unwrap().get();
    let i = locs.get("i").unwrap().get();
    //println!("Indexing {:?}", tup);
    use rush_rt::val::Indexing;
    match Indexing::from_val(&i) {
        Ok(index) => {
            let mut ret = None;
            if let Err(e) = tup.with_index(&index, &mut |val| {
                ret = Some(val.clone());
            }) {
                return e;
            }
            return ret.unwrap_or_else(|| Val::void());
        }
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

pub fn system(interp: &mut Interp, locs: &mut LocalVars) -> Val
{
    let arg = locs.get("args").unwrap();
    let val = util::system(interp, &arg.get());
    val
}

pub fn equals(_: &mut Interp, locs: &mut LocalVars) -> Val
{
    let l = locs.get("l").unwrap();
    let r = locs.get("r").unwrap();
    let val = util::equals(&l.get(), &r.get());
    val
}

pub fn eval(i: &mut Interp, locs: &mut LocalVars, args: Val) -> Val
{
    let cmd = args.iter().flatten().iter().join(" ");
    let mut lex = ::rush_parser::lex::ContextLexer::new();
    let parsed = ::rush_parser::parse::parse(lex.lex(cmd.as_ref()));
    let (v, _) = i.exec_stmt_list(&mut parsed.unwrap(), locs);
    v
}

pub fn mkval_str(i: &mut Interp, locs: &mut LocalVars, cmd: &str) -> Val
{
    let mut lex = ::rush_parser::val_lex::ValueLexer::new();
    let parsed = ::rush_parser::parse::parse(lex.lex(cmd));
    match parsed {
        Ok(ref e) if e.len() == 1 && e[0].0.is_value() => i.from_expr(&e[0], locs).0,
        _ => Val::void(),
    }
}

pub fn mkval(i: &mut Interp, locs: &mut LocalVars, args: Val) -> Val
{
    let cmd = args.iter().flatten().iter().join(" ");
    return mkval_str(i, locs, cmd.as_ref());
}

pub fn source(i: &mut Interp, locs: &mut LocalVars, args: Val) -> Val
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

pub fn keys(_: &mut Interp, locs: &mut LocalVars) -> Val
{
    let args = locs.get("args").unwrap().get();
    //println!("args: {:?}", args);
    let ret = get_tup_dict(&args).list_dict_keys();
    ret.into()
}

pub fn values(_: &mut Interp, locs: &mut LocalVars) -> Val
{
    let args = locs.get("args").unwrap().get();
    //println!("args: {:?}", args);
    let ret = get_tup_dict(&args).list_dict_values();
    ret.into()
}

pub fn range_iter_start(_: &mut Interp, locs: &mut LocalVars) -> Val
{
    let l = locs.get("l").unwrap();
    let r = locs.get("r").unwrap();
    let val = util::range_iter_start(&l.get(), &r.get());
    val
}

pub fn range_iter_next(_: &mut Interp, locs: &mut LocalVars) -> Val
{
    let cur = locs.get("cur").unwrap();
    let l = locs.get("l").unwrap();
    let r = locs.get("r").unwrap();
    let val = util::range_iter_next(&cur.get(), &l.get(), &r.get());
    val
}

pub fn readline_iter_start(i: &mut Interp, locs: &mut LocalVars) -> Val
{
    readline_iter_next(i, locs)
}

pub fn readline_iter_next(_: &mut Interp, _: &mut LocalVars) -> Val
{
    use std::io::{self, BufRead};

    let stdin = io::stdin();
    let ret = match stdin.lock().lines().next() {
        Some(line) => match line {
            Ok(line) => Val::Tup(vec![Val::str("readline::Iter"), Val::str(line)]),
            Err(err) => Val::err_string(format!("{:?}", err)),
        },
        None => Val::void(),
    };
    return ret;
}

pub fn map_iter_start(i: &mut Interp, locs: &mut LocalVars) -> Val
{
    use rush_parser::ast::Span;
    let iter = locs.get("iter").unwrap().get();
    let op = locs.get("op").unwrap().get();
    if iter.len() < 2|| iter.is_err() { return iter }
    let val = iter.iter().nth(1).unwrap().clone();
    let val = i.call(Val::Tup(vec![op.clone(), val.clone()]), Span::zero(), locs);
    Val::Tup(vec![Val::str("map::Iter"), val, iter, op])

}

pub fn map_iter_next(i: &mut Interp, locs: &mut LocalVars) -> Val
{
    use rush_parser::ast::Span;
    let iter = locs.get("iter").unwrap().get();
    let op = locs.get("op").unwrap().get();
    let iter = i.call_next(locs, iter, Span::zero());
    if iter.len() < 2 || iter.is_err() { return iter }
    let val = iter.iter().nth(1).unwrap().clone();
    let val = i.call(Val::Tup(vec![op.clone(), val.clone()]), Span::zero(), locs);
    Val::Tup(vec![Val::str("map::Iter"), val, iter, op])
}

pub fn header_iter_start(i: &mut Interp, locs: &mut LocalVars) -> Val
{
    use rush_parser::ast::Span;
    let mut iter = locs.get("iter").unwrap().get();
    let mut header = locs.get("header").unwrap().get();
    if iter.len() < 2|| iter.is_err() { return iter }
    if header.len() == 0 {
        header = iter.iter().nth(1).unwrap().clone();
        iter = i.call_next(locs, iter, Span::zero());
    }
    let val = iter.iter().nth(1).unwrap().clone();

    Val::Tup(vec![Val::str("header::Iter"), header.pair_with(&val), iter, header])

}

pub fn header_iter_next(i: &mut Interp, locs: &mut LocalVars) -> Val
{
    use rush_parser::ast::Span;
    let iter = locs.get("iter").unwrap().get();
    let header = locs.get("header").unwrap().get();
    let iter = i.call_next(locs, iter, Span::zero());
    if iter.len() < 2|| iter.is_err() { return iter }
    let val = iter.iter().nth(1).unwrap().clone();

    Val::Tup(vec![Val::str("header::Iter"), header.pair_with(&val), iter, header])
}

pub fn list_iter_start(_: &mut Interp, _: &mut LocalVars, args: Val) -> Val
{
    let a = match args.len() {
        0 => Val::void(),
        1 => {
            let v = args.take_tup().unwrap();
            let a = v.into_iter().next().unwrap();
            a
        },
        _ => args,
    };
    let mut ret = match a.take_tup() {
        Ok(mut args) => {
            args.insert(0, Val::str("list::Iter"));
            Val::Tup(args)
        },
        Err(arg) => Val::Tup(vec![Val::str("list::Iter"), arg])
    };
    ret.eval();
    ret
}

pub fn list_iter_next(_: &mut Interp, _: &mut LocalVars, args: Val) -> Val
{
    let args = args.take_tup().unwrap().into_iter().next().unwrap();
    if args.len() <= 2 {
        Val::void()
    } else {
        let mut v = Vec::with_capacity(args.len() - 1);
        let mut count = 0;
        Cow::from(args).for_each_shallow(&mut |val: Cow<Val>| {
            if count != 1 {
                v.push(val.into_owned())
            }
            count += 1;
            return true;
        });
        Val::Tup(v)
    }
}

pub fn cd(_: &mut Interp, locs: &mut LocalVars) -> Val
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

pub fn jobs(i: &mut Interp, _: &mut LocalVars) -> Val
{
    util::jobs(&i.jobs.borrow())
}

pub fn fg(i: &mut Interp, locs: &mut LocalVars) -> Val
{
    let id = locs.get("args").unwrap().get();
    if let Some(id) = id.get_str() {
        if let Ok(id) = str::parse::<usize>(id) {
            return util::fg(&mut i.jobs, id);
        }
    }
    Val::err_str("fg: expected integer argument")
}

pub fn op_bool_status(_: &mut Interp, locs: &mut LocalVars) -> Val
{
    let s = locs.get("s").unwrap();
    if s.with_ref(|x| x.get_str() == Some("0")) {
        Val::str("1")
    } else {
        Val::str("0")
    }
}

pub fn exit(_: &mut Interp, locs: &mut LocalVars) -> Val
{
    let status = locs.get("args");
    let status = if let Some(x) = status {
        x.get().get_str().and_then(|x| str::parse::<i32>(x).ok()).unwrap_or(0)
    } else {
        0
    };
    ::std::process::exit(status)
}
