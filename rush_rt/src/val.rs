use vars::VarRef;
use rush_parser::ast::Span;
use std::ops::Deref;
use std::ascii::AsciiExt;
use std::fmt::{Display, Formatter, Error};
use std::convert::From;
use std::borrow::Cow;
use std::borrow::Cow::*;
use error::{RuntimeError};
use std::io::Write;
use std::rc::Rc;
use regex::Regex;
use rush_pat::range::Range;
use range::RangeExt;
use std::cell::Cell;

#[derive(Debug, Clone, PartialEq)]
pub enum Val {
    Tup(Vec<Val>),
    Str(String),
    Ref(VarRef),
    Embed(Box<Val>),
    Error(Rc<(Vec<Val>, Cell<bool>, Vec<Span>)>),
}

pub trait IntoVal {
    fn into_val(self) -> Val;
}

/*
impl IntoVal for Val {
    fn into_val(self) -> Val {
        return self;
    }
}*/

impl IntoVal for Box<Val> {
    fn into_val(self) -> Val {
        return *self;
    }
}

impl IntoVal for Vec<Val> {
    fn into_val(self) -> Val {
        return Val::Tup(self);
    }
}

impl IntoVal for Range {
    fn into_val(self) -> Val {
        return self.as_val();
    }
}

impl IntoVal for ::rush_parser::parse::ParseError {
    fn into_val(self) -> Val {
        return Val::Str(format!("{:?}", self));
    }
}

impl<'a> IntoVal for &'a str {
    fn into_val(self) -> Val {
        return Val::Str(self.into());
    }
}

impl IntoVal for String {
    fn into_val(self) -> Val {
        return Val::Str(self.into());
    }
}

impl IntoVal for usize {
    fn into_val(self) -> Val {
        return Val::Str(self.to_string());
    }
}

impl IntoVal for i64 {
    fn into_val(self) -> Val {
        return Val::Str(self.to_string());
    }
}

impl<T: IntoVal> IntoVal for Vec<T> {
    fn into_val(self) -> Val {
        let mut ret = Vec::with_capacity(self.len());
        for v in self.into_iter() {
            ret.push(v.into());
        }
        Val::Tup(ret)
    }
}

impl<T: IntoVal> From<T> for Val {
    fn from(this: T) -> Val {
        return this.into_val();
    }
}

impl Display for Val {
    fn fmt(&self, f: &mut Formatter) -> Result<(), Error> {
        use self::Val::*;

        match *self {
            Tup(ref t) => {
                write!(f, "(")?;
                let mut c = 0;
                for ref v in t {
                    if c >= 1 { write!(f, ", ")?; }
                    write!(f, "{}", v)?;
                    c += 1;
                }
                if c == 1 { write!(f, ",")?; }
                write!(f, ")")?;
            },
            Str(ref s) => write!(f, "{}", s)?,
            Ref(ref r) => return r.get_ref().fmt(f),
            Embed(ref e) => return e.fmt(f),
            Error(ref r) => {
                let (ref e, _, ref span) = **r;
                write!(f, "Err({:?}) at {:?}", e, span)?;
            },
        }
        Ok(())
    }
}

#[derive(Clone, Debug)]
pub enum ValIter<'a> {
    Scalar(Option<&'a Val>),
    Tuple(::std::slice::Iter<'a, Val>),
}

#[derive(Clone, Debug)]
pub struct ValFlatIter<'a, T: Clone + Iterator<Item = &'a Val>> {
    iter: T,
}

impl<'a> ValIter<'a> {

    pub fn from_val(val: &'a Val) -> ValIter<'a> {
        use self::Val::*;
        use self::ValIter::*;

        //println!("Create iterator: {:?}", val);
        match *val {
            Tup(ref t) => Tuple(t.iter()),
            _ => Scalar(Some(val)),
        }
    }
}

impl<'a, T: Clone + Iterator<Item = &'a Val>> ValFlatIter<'a, T> {

    pub fn from_iter(iter: T) -> ValFlatIter<'a, T> {
        ValFlatIter{iter: iter}
    }
}

pub trait ValIterOps {
    //type FlatIterType;

    fn flat_len(self) -> usize;
    fn flatten(self) -> Val;
    fn join(self, delim: &str) -> String;
    //fn flat_iter(self) -> Self::FlatIterType;
}

impl<'a, T: Clone + Iterator<Item = &'a Val>> ValIterOps for T {
    fn flat_len(mut self) -> usize {
        use self::Val::*;

        match self.next() {
            Some(&Tup(ref v)) => v.iter().fold(0, |acc, x| acc + x.iter().flat_len()),
            Some(&Ref(ref r)) => r.get_ref().iter().flat_len(),
            Some(_) => 1,
            None => 0,
        }
    }

    /*
    fn flatten_impl(mut self, v: &mut Vec<Val>) {
        use self::Val::*;

        while let Some(val) = self.next() {
            match val {
                &Tup(ref t) => val.iter().flatten_impl(v),
                &Ref(ref r) => r.get_ref().iter().flatten_impl(v),
                x => v.push(x.clone()),
            }
        }
    }*/

    fn flatten(self) -> Val {
        use self::Val::*;

        fn imp<'a, T: Clone + Iterator<Item = &'a Val>>(mut this: T, v: &mut Vec<Val>) {
            while let Some(val) = this.next() {
                match val {
                    &Tup(ref t) => imp(t.iter(), v),
                    &Ref(ref r) => imp(r.get_ref().iter(), v),
                    x => v.push(x.clone()),
                }
            }
        };

        let mut ret = Vec::with_capacity(self.clone().flat_len());;
        imp(self, &mut ret);
        Tup(ret)
    }

    /*
    type FlatIterType = ValFlatIter<'a, T>;
    fn flat_iter(self) -> Self::FlatIterType {
        ValFlatIter::from_iter(self)
    }*/

    fn join(self, delim: &str) -> String {
        let mut first = true;
        let mut ret = "".to_string();
        for s in self.map(|ref v| format!("{}", v)) {
            if !first { ret += delim }
            ret += &s;
            first = false;
        }
        ret
    }
}

impl<'a> Iterator for ValIter<'a> {
    type Item = &'a Val;

    fn next(&mut self) -> Option<Self::Item> {
        use self::ValIter::*;
        use std::mem::replace;

        match self {
            &mut Scalar(ref mut o) => replace(o, None),
            &mut Tuple(ref mut i) => i.next(),
        }
    }
}

impl Val {
    pub fn str<S: Into<String>>(s: S) -> Val {
        Val::Str(s.into())
    }

    pub fn len(&self) -> usize {
        use self::Val::*;

        match self {
            &Tup(ref v) => v.len(),
            _ => 1,
        }
    }

    pub fn with_val<T, F: FnOnce(&Val) -> T>(&self, f: F) -> T {
        use self::Val::*;

        match *self {
            Ref(ref r) => r.get_ref().with_val(f),
            _ => f(self),
        }
    }

    pub fn simplify_shallow(&mut self) {
        use self::Val::*;

        //println!("Simplify: {:?}", self);
        let mut new_val: Option<Val> = None;
        match self {
            &mut Tup(ref mut v) => {
                //println!("Simplify tuple: {:?}", v);
                let mut i = 0;
                while i < v.len() {
                    match v[i] {
                        Error(..) => {
                            let mut tmp = Val::void();
                            ::std::mem::swap(&mut tmp, &mut v[i]);
                            new_val = Some(tmp);
                            break
                        },
                        Embed(..) => {
                            if let Embed(ref mut e) = v[i] {
                                e.simplify_shallow();
                            }
                            v.push(Val::void());
                            if let Embed(box Tup(ev)) = v.swap_remove(i) {
                                v.splice(i..(i+1), ev);
                            }
                        },
                        _ => {},
                    }
                    i += 1;
                }
            },
            &mut Ref(ref n) => {
                let mut nv = n.get().clone();
                nv.simplify_shallow();
                new_val = Some(nv);
            },
            &mut Embed(ref mut e) => e.simplify_shallow(),
            _ => {},
        }

        if let Some(v) = new_val {
            *self = v
        }
    }

    pub fn eval(&mut self) {
        use self::Val::*;

        let mut new_val: Option<Val> = None;
        match self {
            &mut Tup(ref mut v) => {
                let mut i = 0;
                while i < v.len() {
                    v[i].eval();
                    match v[i] {
                        Error(..) => {
                            let mut tmp = Val::void();
                            ::std::mem::swap(&mut tmp, &mut v[i]);
                            new_val = Some(tmp);
                            break
                        },
                        Embed(box Tup(..)) => {
                            v.push(Val::void());
                            if let Embed(box Tup(ev)) = v.swap_remove(i) {
                                v.splice(i..(i+1), ev);
                            } else {
                                unreachable!();
                            }
                        },
                        _ => {},
                    }
                    i += 1;
                }
            },
            &mut Ref(ref n) => {
                let mut nv = n.get().clone();
                nv.eval();
                new_val = Some(nv);
            },
            &mut Embed(ref mut e) => e.eval(),
            _ => {},
        }

        if let Some(v) = new_val {
            *self = v
        }
    }

    pub fn get_int(&self) -> Option<i64> {
        if let &Val::Str(ref s) = self {
            if let Ok(i) = str::parse::<i64>(s.as_str()) {
                Some(i)
            } else {
                None
            }
        } else {
            None
        }
    }

    pub fn get_str(&self) -> Option<&str> {
        match *self {
            Val::Str(ref s) => Some(s),
            Val::Tup(ref t) if t.len() == 1 => t[0].get_str(),
            _ => None,
        }
    }

    pub fn get_cowstr(&self) -> Option<Cow<str>> {
        match *self {
            Val::Str(ref s) => Some(Borrowed(s)),
            Val::Ref(ref r) => r.get_ref().get_string().map(|x| { Owned(x) }),
            Val::Tup(ref t) if t.len() == 1 => t[0].get_cowstr(),
            _ => None,
        }
    }

    pub fn get_string(&self) -> Option<String> {
        match *self {
            Val::Str(ref s) => Some(s.clone()),
            Val::Ref(ref r) => r.get_ref().get_string(),
            Val::Tup(ref t) if t.len() == 1 => t[0].get_string(),
            _ => None,
        }
    }

    pub fn take_str(self) -> Option<String> {
        if let Val::Str(s) = self {
            Some(s)
        } else {
            None
        }
    }

    pub fn get_tup(&self) -> Option<&Vec<Val>> {
        if let &Val::Tup(ref v) = self {
            Some(v)
        } else {
            None
        }
    }

    pub fn get_tup_mut(&mut self) -> Option<&mut Vec<Val>> {
        if let &mut Val::Tup(ref mut v) = self {
            Some(v)
        } else {
            None
        }
    }

    pub fn take_tup(self) -> Option<Vec<Val>> {
        if let Val::Tup(v) = self {
            Some(v)
        } else {
            None
        }
    }

    pub fn get_1char(&self) -> Option<char> {
        if let Some(s) = self.get_str() {
            if s.len() == 1 {
                Some(s.chars().nth(0).unwrap())
            } else {
                None
            }
        } else {
            None
        }
    }

    pub fn get_1ascii(&self) -> Option<u8> {
        if let Some(c) = self.get_1char() {
            if c.is_ascii() {
                Some(c as u8)
            } else {
                None
            }
        } else {
            None
        }
    }

    pub fn true_() -> Val {
        Val::Str("1".into())
    }

    pub fn false_() -> Val {
        Val::Str("0".into())
    }

    pub fn void() -> Val {
        Val::Tup(vec![])
    }

    pub fn err_str(val: &str) -> Val {
        Self::custom_err(vec![Val::str(val)], None)
    }

    pub fn err_string(val: String) -> Val {
        Self::custom_err(vec![Val::Str(val)], None)
    }

    pub fn ok(val: Val) -> Val {
        Val::Tup(vec![Val::str("Ok"), val])
    }

    pub fn custom_err(v: Vec<Val>, span: Option<Span>) -> Val {
        Val::err(RuntimeError::CustomError(v), span)
    }
    pub fn err(e: RuntimeError, span: Option<Span>) -> Val {
        let v = match e {
            RuntimeError::CustomError(v) => v,
            _ => vec![e.into()],
        };
        if let Some(span) = span {
            Val::Error(Rc::new((v, false.into(), vec![span])))
        } else {
            Val::Error(Rc::new((v, false.into(), vec![])))
        }
    }

    pub fn some(val: Val) -> Val {
        Val::Tup(vec![Val::str("Some"), val])
    }

    pub fn none() -> Val {
        Val::Tup(vec![Val::str("None")])
    }

    pub fn status(code: i64) -> Val {
        Val::Tup(vec![Val::str("Status"), Val::str(code.to_string())])
    }

    pub fn iter(&self) -> ValIter {
        ValIter::from_val(self)
    }

    pub fn unhandled(&self) -> bool {
        if let Val::Error(ref e) = *self {
            if e.1.get() == false {
                writeln!(&mut ::std::io::stderr(), "Warning: unhandled error {:?}", self).unwrap();
                return true;
            }
        }
        return false;
    }
}

impl From<bool> for Val {
    fn from(b: bool) -> Val {
        if b {
            Val::true_()
        } else {
            Val::false_()
        }
    }
}

impl<'a> From<Val> for Cow<'a, Val> {
    fn from(v: Val) -> Self {
        Owned(v)
    }
}

impl<'a> From<&'a Val> for Cow<'a, Val> {
    fn from(v: &'a Val) -> Self {
        Borrowed(v)
    }
}

pub trait ForEachShallowFn : FnMut(Cow<Val>) -> bool {}
impl<T> ForEachShallowFn for T where T: FnMut(Cow<Val>) -> bool {}

pub trait ForEachFn : FnMut(Cow<str>, usize) -> bool {}
impl<T> ForEachFn for T where T: FnMut(Cow<str>, usize) -> bool {}

pub trait ForEachPairsFn : FnMut(Option<Cow<str>>, Option<&str>, usize) -> bool {}
impl<T> ForEachPairsFn for T where T: FnMut(Option<Cow<str>>, Option<&str>, usize) -> bool {}

use std::iter::Peekable;

pub trait ValIterator : Iterator {}
impl<'a, T> ValIterator for Peekable<T> where T: Iterator<Item = &'a Val> {}

pub trait InternalIterable {
    fn for_each<F>(self, f: &mut F) -> bool where F: ForEachFn;
    fn for_each_shallow<F>(self, f: &mut F) -> bool where F: ForEachShallowFn;
    fn for_each_pairs<F>(self, other: &Val, f: &mut F) -> bool where F: ForEachPairsFn;
}

#[derive(Debug,Eq,PartialEq,PartialOrd,Ord,Copy,Clone,Default)]
struct Depth(usize, usize, bool, bool);

impl Depth {
    fn dep(&self) -> usize {
        self.0 - self.1
    }

    fn inc(self) -> Depth {
        if self.2 {
            Depth(self.0 + 1, self.1 + 1, false, false)
        } else {
            Depth(self.0 + 1, self.1, false, false)
        }
    }

    fn embed(self) -> Depth {
        Depth(self.0, self.1, true, false)
    }

    fn enter_ref(self) -> Depth {
        Depth(self.0, self.1, self.2, true)
    }

    fn is_emb(&self) -> bool {
        self.1 > 0 || self.2
    }

    fn is_ref(&self) -> bool {
        self.3
    }

    fn equiv(&self, oth: Self) -> bool {
        self.dep() == oth.dep()
    }
}

impl<'a> InternalIterable for Cow<'a, Val> {
    fn for_each_shallow<F>(self, f: &mut F) -> bool where F: ForEachShallowFn {
        fn imp<'a, F>(this: Cow<'a, Val>, f: &mut F, depth: Depth) -> bool where F: ForEachShallowFn {
            use self::Val::*;

            match this {
                Owned(Str(_)) | Borrowed(&Str(_))
                    => { return f(this); },
                Owned(Tup(t)) => {
                    if depth.dep() > 0 {
                        return f(Owned(Tup(t)))
                    } else {
                        for x in t {
                            if !imp(Owned(x), f, depth.inc()) { return false }
                        }
                    }
                    return true;
                },
                Borrowed(&Tup(ref t)) => {
                    if depth.dep() > 0 {
                        return f(this)
                    } else {
                        for x in t {
                            if !imp(Borrowed(x), f, depth.inc()) { return false }
                        }
                    }
                    return true;
                },
                Owned(Embed(e)) => {
                    return imp(Owned(*e), f, depth.embed());
                },
                Borrowed(&Embed(ref e)) => {
                    return imp(Borrowed(&*e), f, depth.embed());
                },
                Owned(Ref(r)) => {
                    let r = r.get_ref();
                    return imp(Borrowed(r.deref()), f, depth.enter_ref());
                },
                Borrowed(&Ref(ref r)) => {
                    let vref = r.clone();
                    let r = vref.get_ref();
                    return imp(Borrowed(r.deref()), f, depth.enter_ref());
                },
                Owned(Error(ref e)) | Borrowed(&Error(ref e)) => {
                    e.1.set(true);
                    let depth = depth.inc();
                    f(Owned("Err!".into()));
                    for x in e.0.iter() {
                        if !imp(Borrowed(x), f, depth) { return false }
                    }
                    return true;
                },
            };
        };
        return imp(self, f, Depth::default())
    }

    fn for_each<F>(self, f: &mut F) -> bool where F: ForEachFn {
        fn imp<'a, F>(this: Cow<'a, Val>, f: &mut F, depth: usize, flatten: usize) -> bool where F: ForEachFn {
            use self::Val::*;

            match this {
                Owned(Str(s)) => { return f(Owned(s), depth); },
                Borrowed(&Str(ref s)) => { return f(Borrowed(s), depth); },
                Owned(Tup(t)) => {
                    for x in t {
                        let (dep, flat) = if flatten > 0 { (depth, flatten - 1) } else { (depth + 1, 0) };
                        if !imp(Owned(x), f, dep, flat) { return false }
                    }
                    return true;
                },
                Borrowed(&Tup(ref t)) => {
                    for ref x in t {
                        let (dep, flat) = if flatten > 0 { (depth, flatten - 1) } else { (depth + 1, 0) };
                        if !imp(Borrowed(x), f, dep, flat) { return false }
                    }
                    return true;
                },
                Owned(Embed(e)) => {
                    return imp(Owned(*e), f, depth, flatten + 1);
                },
                Borrowed(&Embed(ref e)) => {
                    return imp(Borrowed(&*e), f, depth, flatten + 1);
                },
                Owned(Ref(r)) => {
                    let r = r.get_ref();
                    return imp(Borrowed(r.deref()), f, depth, flatten);
                },
                Borrowed(&Ref(ref r)) => {
                    let vref = r.clone();
                    let r = vref.get_ref();
                    return imp(Borrowed(r.deref()), f, depth, flatten);
                },
                Owned(Error(ref e)) | Borrowed(&Error(ref e)) => {
                    e.1.set(true);
                    let depth = depth + 1;
                    f(Owned("Err!".into()), depth);
                    for x in e.0.iter() {
                        if !imp(Borrowed(x), f, depth, flatten) { return false }
                    }
                    return true;
                },
            };
        };
        return imp(self, f, 0, 0)
    }

    fn for_each_pairs<F>(self, oth: &Val, f: &mut F) -> bool where F: ForEachPairsFn {
        fn imp<'a, 'b, IL, IR, F>(il: &mut Peekable<IL>, ir: &mut Peekable<IR>, f: &mut F, dl: Depth, dr: Depth) -> bool
            where IL: ExactSizeIterator + Iterator<Item=&'a Val>, IR: ExactSizeIterator + Iterator<Item=&'b Val>, F: ForEachPairsFn {
            use self::Val::*;
            loop {
                //println!("{} {}  {:?} {:?}  {:?}  {:?}", l_len, r_len, dl, dr, il.peek(), ir.peek());
                match (il.peek(), ir.peek()) {
                    (Some(&&Ref(ref r)), _) => {
                        let r = r.get_ref();
                        let mut iter = vec![&*r].into_iter().peekable();
                        if !imp(&mut iter, ir, f, dl.enter_ref(), dr) { return false; }

                        il.next();

                        //println!("Ref Left next {:?}", il.next());
                    },
                    (_, Some(&&Ref(ref r))) => {
                        let r = r.get_ref();
                        let mut iter = vec![&*r].into_iter().peekable();
                        if !imp(il, &mut iter, f, dl, dr.enter_ref()) { return false; }

                        ir.next();

                        //println!("Ref Right next {:?}", ir.next());
                    },
                    (Some(&&Embed(ref r)), _) => {
                        let mut iter = vec![&**r].into_iter().peekable();
                        if !imp(&mut iter, ir, f, dl.embed(), dr) { return false; }

                        il.next();

                        //println!("Embed Left next {:?}", il.next());
                    },
                    (_, Some(&&Embed(ref r))) => {
                        let mut iter = vec![&**r].into_iter().peekable();
                        if !imp(il, &mut iter, f, dl, dr.embed()) { return false; }

                        ir.next();

                        //println!("Embed Right next {:?}", ir.next());
                    },
                    (Some(&&Tup(ref l)), Some(&&Tup(ref r))) => {
                        let mut liter = l.iter().peekable();
                        let mut riter = r.iter().peekable();
                        let depl = dl.inc();
                        let depr = dr.inc();
                        if !depl.equiv(depr) { return false };
                        //println!("Tup launch: {:?} {:?}  {:?}  {:?}", depl, depr, liter.peek(), riter.peek());
                        if !imp(&mut liter, &mut riter, f, depl, depr) { return false; }
                        //println!("Tup return: {:?} {:?}  {:?}  {:?}", depl, depr, liter.peek(), riter.peek());
                        if !liter.peek().is_none() { return false; }
                        if !riter.peek().is_none() { return false; }

                        il.next();
                        ir.next();
                        //println!("Tup Tup next {:?} {:?}", il.next(), ir.next());
                    },
                    /*
                    (Some(&&Tup(ref l)), Some(&&Str(ref r))) if l.len() == 1 => {
                        if sat0(dr) != sat0(dl) { return false };
                        if let Some(s) = l[0].get_str() {
                            if !f(Some(Cow::from(s)), Some(r.as_ref()), sat0(dr)) { return false }
                        } else {
                            return false;
                        }

                        il.next();
                        ir.next();
                    },
                    (Some(&&Str(ref l)), Some(&&Tup(ref r))) if r.len() == 1 => {
                        if sat0(dr) != sat0(dl) { return false };
                        if let Some(s) = r[0].get_str() {
                            if !f(Some(Cow::from(l.as_ref())), Some(s), sat0(dl)) { return false }
                        } else {
                            return false;
                        }

                        il.next();
                        ir.next();
                    },
                    */
                    (Some(&&Str(_)), Some(&&Tup(ref r))) => {
                        let mut riter = r.iter().peekable();
                        let depr = dr.inc();
                        if !dl.equiv(depr) { return false };
                        if !imp(il, &mut riter, f, dl, depr) { return false; }
                        if !riter.peek().is_none() { return false; }

                        ir.next();

                        //println!("Str Tup next {:?}", ir.next());
                    },
                    (Some(&&Tup(ref l)), Some(&&Str(_))) => {
                        let mut liter = l.iter().peekable();
                        let depl = dl.inc();
                        if !dr.equiv(depl) { return false };
                        if !imp(&mut liter, ir, f, depl, dr) { return false; }
                        if !liter.peek().is_none() { return false; }

                        il.next();

                        //println!("Tup Str next {:?}", il.next());
                    },
                    (Some(&&Str(ref l)), Some(&&Str(ref r))) => {
                        if !dl.equiv(dr) { return false };
                        if !f(Some(Cow::from(l.as_ref())), Some(r.as_ref()), dl.dep()) { return false; }

                        il.next();
                        ir.next();

                        //println!("Str Str next {:?} {:?}", il.next(), ir.next());
                    },
                    (Some(&&Str(ref l)), None) if !dr.is_emb() && !dr.is_ref() => {
                        if !f(Some(Cow::from(l.as_ref())), None, dl.dep()) { return false; }

                        il.next();
                        ir.next();

                        //println!("Str None next {:?} {:?}", il.next(), ir.next());
                    },
                    (None, Some(&&Str(ref r))) if !dl.is_emb() && !dl.is_ref() => {
                        if !f(None, Some(r.as_ref()), dl.dep()) { return false; }

                        il.next();
                        ir.next();

                        //println!("None Str next {:?} {:?}", il.next(), ir.next());
                    },
                    (None, _) | (_, None) => return true,
                    (Some(&&Error(ref _e)), _) | (_, Some(&&Error(ref _e))) => {
                        unimplemented!();
                    }
                }
            }
        };
        let mut il = vec![&*self].into_iter().peekable();
        let mut ir = vec![oth].into_iter().peekable();
        return imp(&mut il, &mut ir, f, Depth::default(), Depth::default())
    }
}

impl From<Regex> for Val {
    fn from(f: Regex) -> Val {
        use self::Val::*;

        Tup(vec![Val::str("Regex"), Val::str(f.as_str())])
    }
}

impl<'a> From<&'a Regex> for Val {
    fn from(f: &'a Regex) -> Val {
        use self::Val::*;

        Tup(vec![Val::str("Regex"), Val::str(f.as_str())])
    }
}
