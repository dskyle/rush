use vars::{LocalVars, Binder, Resolver};
use val::Val;
use error::{RuntimeError, Res};
use std::rc::Rc;
use std::clone::Clone;
use std::borrow::Cow;
use std::borrow::Cow::*;
use rush_pat::pat::{Pat, RegexEq};
use rush_pat::subsume::{Subsumption, Subsumes};
use rush_parser::lex::is_identifier;
use regex::Regex;
use std::convert::TryFrom;
use std::iter::IntoIterator;

pub static ERR_NAME : &str = "Err!";

impl TryFrom<Val> for Regex {
    type Error = RuntimeError;

    fn try_from(f: Val) -> Res<Regex> {
        use self::RuntimeError::*;
        use self::Val::*;
        match f {
            Tup(t) => {
                if t.len() != 2 { return Err(InvalidRegexVal(Box::new(Tup(t)), "Expected 2-length tuple")) }
                let mut t = t.into_iter();
                let id = t.next().unwrap();
                let rex = t.next().unwrap();
                match id {
                    Str(id) => {
                        if id != "Regex" { return Err(InvalidRegexVal(Box::new(Str(id)), "Expected string \"Regex\"")) }
                        match rex {
                            Str(rex) => {
                                Regex::new(&rex).map_err(|e| InvalidRegex(format!("{}", e), "Bad regex syntax"))
                            },
                            _ => Err(InvalidRegexVal(Box::new(rex), "Expected regex string")),
                        }
                    },
                    _ => Err(InvalidRegexVal(Box::new(id), "Expected string \"Regex\"")),
                }
            },
            _ => Err(InvalidRegexVal(Box::new(f), "Expected 2-length tuple")),
        }
    }
}

pub trait ValMatcher {
    fn do_match(&self, val: Cow<Val>, b: &mut LocalVars) -> bool;
    fn do_match_unchecked(&self, val: Cow<Val>, b: &mut LocalVars) -> bool;
}

fn process_embed_check<'a, PIter: Clone + Iterator<Item = &'a Pat>>(
            this: &Pat,
            piter: PIter,
            l: &Pat,
            val: &Val,
            depth: usize) -> (PIter, bool) {
    match val {
        &Val::Tup(ref v) => {
            //println!("In Embed::Tup: {:?}", v);
            let niter = v.iter();
            return process_tup_check(this, piter, niter, depth + 1);
        },
        &Val::Ref(ref r) => {
            //println!("In Embed::Tup::Ref: {:?}", r);
            return r.with_ref(|x| process_embed_check(this, piter, l, x, depth));
        },
        x => return (piter, l.subsumes(x) == Subsumption::Contains),
    }
}
fn process_tup_check<'a, 'b, PIter: Clone + Iterator<Item = &'a Pat>, VIter: Clone + Iterator<Item = &'b Val>>(
            this: &Pat,
            mut piter: PIter,
            mut viter: VIter,
            depth: usize) -> (PIter, bool) {
    loop {
        let prev_piter = piter.clone();
        let l = piter.next();
        //println!("l: {:?}", &l);
        match l {
            Some(&Pat::Wild(..)) => { while piter.next().is_some() {} return (piter, true); },
            Some(l) => {
                {
                    let r = viter.clone().next();
                    //println!("r: {:?}", &r);
                    match r {
                        Some(&Val::Embed(ref r)) => {
                            //println!("In Embed: {:?}", r);
                            let (i, ret) = process_embed_check(this, prev_piter, l, r, depth);
                            if !ret {
                                return (i, ret);
                            } else {
                                piter = i;
                            }
                        },
                        Some(r) => {
                            if l.subsumes(r) == Subsumption::Disjoint {
                                return (piter, false)
                            }
                        },
                        None => return (prev_piter, if depth == 0 { false } else { true }),
                    }
                }
                viter.next();
            },
            None => return (piter, viter.next().is_none()),
        }
    }
}

fn bind_refs_none(this: &Pat, b: &mut LocalVars) {
    match this {
        &Pat::ID(ref s) | &Pat::Bind(ref s, _) => { b.bind(s.as_ref(), Val::void()); },
        &Pat::Tup(ref v) => for p in v { bind_refs_none(p, b) },
        &Pat::Rex(RegexEq(ref r)) => {
            let mut cap_num = 0;
            for c in r.capture_names() {
                if let Some(c) = c {
                    if is_identifier(c) {
                        b.bind(c, Val::void());
                    }
                }
                b.bind(format!("_{}", cap_num), Val::void());
                cap_num += 1;
            }
        },
        &Pat::Wild(ref v) => for p in v { bind_refs_none(p, b) },
        _ => {}
    }
}

fn do_binding<T: Into<String> + AsRef<str> + ::std::fmt::Debug>(name: T, val: Cow<Val>, b: &mut LocalVars, wrap_some: bool) {
    if name.as_ref() == "_" {
        //println!("Ignore {:?}", val);
    } else {
        let mut val = val.into_owned();
        val.simplify_shallow();
        if wrap_some {
            //println!("Bind optional {:?} to ({:?})", name, val);
            let var = b.get(name.as_ref()).expect("Variable should already exist in optional arg binding");
            var.with_mut(|x| {
                if let Val::Tup(ref mut v) = *x {
                    //println!("Existing tuple: {:?}", v);
                    v.push(val);
                } else {
                    unreachable!();
                }
            });
            //b.bind(name, Val::Tup(vec![Val::str("Some"), val]));
        } else {
            //println!("Bind {:?} to {:?}", name, val);
            b.bind(name.into(), val);
        }
    }
}

fn search_wild_matches(vec: &Vec<Pat>, val: Cow<Val>, b: &mut LocalVars) {
    for ref p in vec {
        if p.subsumes(val.as_ref()) == Subsumption::Contains {
            do_match_impl(p, val, b, true);
            break;
        }
    }
}

fn process_embed_matches<'a, PIter: Clone + Iterator<Item = &'a Pat>>(
            this: &Pat,
            piter: PIter,
            l: &Pat,
            val: Cow<Val>,
            b: &mut LocalVars,
            wrap_some: bool) -> (bool, PIter) {
    match val {
        Borrowed(&Val::Tup(ref v)) => {
            let niter = v.iter().map(Cow::from);
            //println!("Calling process_tup_matches (Embed|Tup)");
            return (true, process_tup_matches(this, piter, niter, b, wrap_some));
        },
        Owned(Val::Tup(v)) => {
            let niter = v.into_iter().map(Cow::from);
            //println!("Calling process_tup_matches (Embed|Tup)");
            return (true, process_tup_matches(this, piter, niter, b, wrap_some));
        },
        Borrowed(&Val::Ref(ref r)) => {
            return r.with_ref(|x| process_embed_matches(this, piter, l, Borrowed(x), b, wrap_some));
        },
        Owned(Val::Ref(r)) => {
            return r.with_ref(|x| process_embed_matches(this, piter, l, Borrowed(x), b, wrap_some));
        },
        x => { do_match_impl(l, x, b, wrap_some); return (false, piter) },
    }
}

fn process_tup_matches<'a, 'b, PIter: Clone + Iterator<Item = &'a Pat>, VIter: Iterator<Item = Cow<'b, Val>>>(
            this: &Pat,
            mut piter: PIter,
            mut viter: VIter,
            b: &mut LocalVars,
            wrap_some: bool) -> PIter {
    loop {
        let l = piter.clone().next();
        //println!("Outer Loop: {:?}", l);
        match l {
            Some(l) => {
                let is_wild = { if let &Pat::Wild(..) = l { true } else { false } };
                let wrap_some = wrap_some || is_wild;
                {
                    let r = viter.next();
                    //println!("Val: {:?}", r);
                    match r {
                        Some(Borrowed(&Val::Embed(ref r))) => {
                            let (b, i) =  process_embed_matches(this, piter, l, Borrowed(&**r), b, wrap_some);
                            piter = i;
                            if b { continue; }
                        },
                        Some(Owned(Val::Embed(r))) => {
                            let (b, i) =  process_embed_matches(this, piter, l, Owned(*r), b, wrap_some);
                            piter = i;
                            if b { continue; }
                        },
                        Some(r) => { do_match_impl(l, r, b, wrap_some); },
                        None => break,
                    };
                }
                let l = piter.clone().next();
                let is_wild = { if let Some(&Pat::Wild(..)) = l { true } else { false } };
                if !is_wild { piter.next(); }
            },
            None => break,
        }
    }
    return piter;
}

fn do_match_impl(this: &Pat, val: Cow<Val>, b: &mut LocalVars, wrap_some: bool) -> bool {
    use self::Pat::*;

    //println!("Binding {:?} from {:?}", this, val);
    match this {
        &ID(ref s) | &Bind(ref s, _) => {
            do_binding(s.as_ref(), val, b, wrap_some);
        },
        &Tup(ref pt) => match val {
                Borrowed(&Val::Tup(ref vt)) => {
                    let piter = pt.iter();
                    let viter = vt.iter().map(Cow::from);
                    //println!("Calling process_tup_matches (Tup)");
                    process_tup_matches(this, piter, viter, b, wrap_some);
                },
                Owned(Val::Tup(vt)) => {
                    let piter = pt.iter();
                    let viter = vt.into_iter().map(Cow::from);
                    //println!("Calling process_tup_matches (Tup)");
                    process_tup_matches(this, piter, viter, b, wrap_some);
                },
                Borrowed(&Val::Error(ref e)) => if pt.len() > 1 && pt[0].get_atom() == Some(ERR_NAME) {
                    e.1.set(true);
                    let vt = &e.0;
                    let mut piter = pt.iter();
                    piter.next();
                    let viter = vt.iter().map(Cow::from);
                    //println!("Calling process_tup_matches (Tup)");
                    process_tup_matches(this, piter, viter, b, wrap_some);
                },
                Owned(Val::Error(e)) => if pt.len() > 1 && pt[0].get_atom() == Some(ERR_NAME) {
                    let mut piter = pt.iter();
                    piter.next();
                    match Rc::try_unwrap(e) {
                        Ok(e) => {
                            let viter = e.0.into_iter().map(Cow::from);
                            //println!("Calling process_tup_matches (Tup)");
                            process_tup_matches(this, piter, viter, b, wrap_some);
                        },
                        Err(e) => {
                            e.1.set(true);
                            let viter = e.0.iter().map(Cow::from);
                            //println!("Calling process_tup_matches (Tup)");
                            process_tup_matches(this, piter, viter, b, wrap_some);
                        }
                    }
                },
                Owned(Val::Str(_)) | Borrowed(&Val::Str(_)) => {
                    if pt.len() == 1 {
                        do_match_impl(&pt[0], val, b, wrap_some);
                    }
                },
                Owned(Val::Ref(ref r)) | Borrowed(&Val::Ref(ref r)) => {
                    r.with_ref(|x| do_match_impl(this, Borrowed(x), b, wrap_some));
                },
                _ => {}
            },
        &Rex(RegexEq(ref r)) => {
            //println!("regex do for {:?}", val);
            if let Some(s) = val.get_string() {
                //println!("regex for {:?}", s);
                for caps in r.captures_iter(&s) {
                    let mut cap_num = 0;
                    //println!("regex for caps {:?}", caps);
                    for x in caps.iter().zip(r.capture_names()) {
                        //println!("regex for cap {:?}", x);
                        match x.0 {
                            Some(m) => {
                                //println!("{:?}[{}]: {:?}", x.1, cap_num, m);
                                if let Some(name) = x.1 {
                                    if is_identifier(name) {
                                        do_binding(name, Val::Str(m.as_str().into()).into(), b, true)
                                    }
                                }

                                do_binding(format!("_{}", cap_num), Val::Str(m.as_str().into()).into(), b, true);
                            },
                            _ => {}
                        }
                        cap_num += 1
                    }
                }
            }
        }
        &Wild(ref vec) => {
            search_wild_matches(vec, val, b);
        }
        _ => {}
    }

    return true;
}

impl Subsumes<Val> for Pat {
    fn subsumes(&self, val: &Val) -> Subsumption {
        use self::Pat::*;
        use self::Subsumption::*;

        //println!("Checking {:?} {:?}", self, val);
        match (self, val) {
            (&Wild(..), _) => Contains,
            (&ID(_), _) => Contains,
            (_, &Val::Ref(ref var)) => var.with_ref(|x| self.subsumes(x)),
            (_, &Val::Embed(ref val)) => self.subsumes(&**val),
            (&Tup(ref pt), &Val::Tup(ref vt)) => {
                let piter = pt.iter();
                let viter = vt.iter();
                let (mut pi, ret) = process_tup_check(self, piter, viter, 0);
                let done = pi.next().is_none();
                //println!("Returning for {:?} ?= {:?}  ===>  {:?} {:?}", self, val, ret, done);
                if ret && done { Contains } else { Disjoint }
            },
            (&Tup(ref pt), &Val::Error(ref e)) => {
                if pt.len() >= 1 && pt[0].get_atom() == Some(ERR_NAME) {
                    let vt = &e.0;
                    let mut piter = pt.iter();
                    piter.next();
                    let viter = vt.iter();
                    let (mut pi, ret) = process_tup_check(self, piter, viter, 0);
                    let done = pi.next().is_none();
                    //println!("Returning for {:?} ?= {:?}  ===>  {:?} {:?}", self, val, ret, done);
                    if ret && done { Contains } else { Disjoint }
                } else {
                    Disjoint
                }
            },
            (_, &Val::Tup(ref t)) if t.len() == 1 => self.subsumes(&t[0]),
            (&Bind(_, ref p), _) => p.subsumes(val),
            (&Str(ref s), &Val::Str(ref o)) => (&s[..]).subsumes(&o[..]),
            (&Str(_), _) => Disjoint,
            (&Rng(ref r), &Val::Str(ref o)) => r.subsumes(&o[..]),
            (&Rng(_), _) => Disjoint,
            (&Rex(ref r), &Val::Str(ref o)) => r.0.subsumes(&o[..]),
            (&Rex(_), _) => Disjoint,
            (&StrList(ref l), &Val::Str(ref o)) => l.subsumes(&o[..]),
            (&StrList(_), _) => Disjoint,
            //(&Tup(ref pt), _) if pt.len() == 1 || (pt.len() > 1 && pt[1].is_wild()) => pt[0].subsumes(val),
            (&Tup(_), _) => Disjoint,
        }
    }
}

impl Subsumes<Pat> for Val {
    fn subsumes(&self, pat: &Pat) -> Subsumption {
        pat.subsumes(self).reverse()
    }
}

impl ValMatcher for Pat {
    fn do_match(&self, val: Cow<Val>, b: &mut LocalVars) -> bool {
        if self.subsumes(val.as_ref()) == Subsumption::Disjoint {
            return false;
        }

        self.do_match_unchecked(val, b)
    }

    fn do_match_unchecked(&self, val: Cow<Val>, b: &mut LocalVars) -> bool {
        bind_refs_none(self, b);

        do_match_impl(self, val, b, false)
    }

}

#[test]
fn test_ordering() {
    use self::Pat::*;
    use self::Subsumption::*;

    let i1 = ID("a".into());
    let i2 = ID("b".into());
    let s1 = Str("foo".into());
    let s2 = Str("bar".into());
    assert_eq!(i1.subsumes(&i2), Some(Overlaps));
    assert_eq!(s1.subsumes(&s2), None);
    assert_eq!(i1.subsumes(&s1), Some(Contains));
    assert_eq!(s1.subsumes(&i1), Some(ContainedBy));

    let t1 = Tup(vec![s1, i1]);
    let t2 = Tup(vec![s2, i2]);
    assert_eq!(t1.subsumes(&t2), None);
    assert_eq!(t1.subsumes(&t1), Some(Overlaps));

    let w1 = Wild(vec![]);
    let w2 = ID("a".into());
    assert_eq!(w1.subsumes(&w2), Some(Contains));

    let f1 = Tup(vec![Str("asdf".into()), Bind("a".into(), Box::new(Str("zxcv".into()))), Wild(vec![])]);
    let f2 = Tup(vec![Str("asdf".into()), Bind("a".into(), Box::new(Str("zxcv".into()))), ID("a".into())]);
    println!("{:?}", f1);
    println!("{:?}", f2);
    assert_eq!(f1.subsumes(&f2), Some(Contains));
}
