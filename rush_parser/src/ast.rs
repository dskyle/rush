use std::ops::Add;
use std::ops::AddAssign;
use std::ops::Deref;
use std::fmt;
use std::ascii::AsciiExt;
use rush_pat::pat::{Pat, RegexEq};
use std::cell::RefCell;
use std::borrow::Cow;
use std::borrow::Cow::*;
use rush_pat::range::{Range};
use parse::{ParseError, Res};

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub enum SubsMode {
    Void,
    Status,
    Insert,
    Embed,
    String,
}

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub enum TupleStyle {
    Spaced,
    Comma,
    Named,
}

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub enum ImportScope {
    Global,
    Sys,
}

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub enum SetOp {
    Assign,
    AssignIfNull,
    Suffix,
    Prefix,
}

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub enum  ManOp {
    Merge{into: u32, from: u32},
}

#[derive(Clone, Copy, Eq, PartialEq, Hash)]
pub struct Pos {
    pub line: usize,
    pub col: usize,
}

impl Pos {
    pub fn new(l: usize, c: usize) -> Pos {
        Pos{line: l, col: c}
    }
}

impl Add<(usize, usize)> for Pos {
    type Output = Pos;
    fn add(self, o: (usize, usize)) -> Pos {
        //println!("adding {:?}", o);
        if o.0 == 0 {
            Pos{line: self.line, col: self.col + o.1}
        } else {
            Pos{line: self.line + o.0, col: o.1}
        }
    }
}

impl fmt::Debug for Pos {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}:{:?}", self.line, self.col)
    }
}


#[derive(Clone, Copy, Eq, PartialEq, Hash)]
pub struct Span {
    pub l: Pos,
    pub r: Pos,
}

impl Span {
    pub fn new(l: Pos, r: Pos) -> Span {
        Span{l: l, r: r}
    }
}

impl AddAssign<usize> for Span {
    fn add_assign(&mut self, a: usize) {
        self.r.col += a;
    }
}

impl Add<usize> for Span {
    type Output = Span;

    fn add(mut self, a: usize) -> Span {
        self += a;
        self
    }
}

impl fmt::Debug for Span {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "[{:?}, {:?}]", self.l, self.r)
    }
}

#[derive(Clone, PartialEq)]
pub struct ExprS(pub Expr, pub Span);

impl fmt::Debug for ExprS {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}{:?}", self.0, self.1)
    }
}


#[derive(Debug, Clone, PartialEq)]
pub enum ASTRange {
    All,
    From(Box<ExprS>),
    Till(Box<ExprS>),
    Within(Box<ExprS>, Box<ExprS>),
}

impl ASTRange {
    pub fn from_ast_range(r: Cow<ASTRange>) -> Res<Range> {
        use self::Range::*;
        use self::ParseError::*;

        match *r {
            ASTRange::All => return Ok(All),
            ASTRange::From(ref from) => {
                if let Some(from) = from.get_int() {
                    return Ok(FromInt(from))
                }
                if let Some(from) = from.get_1ascii() {
                    return Ok(FromAscii(from))
                }
                if let Some(from) = from.get_atom() {
                    return Ok(FromStr(from))
                }
            }
            ASTRange::Till(ref to) => {
                if let Some(to) = to.get_int() {
                    return Ok(TillInt(to))
                }
                if let Some(to) = to.get_1ascii() {
                    return Ok(TillAscii(to))
                }
                if let Some(to) = to.get_atom() {
                    return Ok(TillStr(to))
                }
            }
            ASTRange::Within(ref from, ref to) => {
                if let Some(from) = from.get_int() {
                    if let Some(to) = to.get_int() {
                        return Ok(WithinInt(from, to))
                    }
                }
                if let Some(from) = from.get_1ascii() {
                    if let Some(to) = to.get_1ascii() {
                        return Ok(WithinAscii(from, to))
                    }
                }
                if let Some(from) = from.get_atom() {
                    if let Some(to) = to.get_atom() {
                        return Ok(WithinStr(from, to))
                    }
                }
            },
        }
        return Err(InvalidRange("Invalid range; must be between scalar strings"))
    }
}

impl<'a> From<ASTRange> for Cow<'a, ASTRange> {
    fn from(v: ASTRange) -> Self {
        Owned(v)
    }
}

impl<'a> From<&'a ASTRange> for Cow<'a, ASTRange> {
    fn from(v: &'a ASTRange) -> Self {
        Borrowed(v)
    }
}


#[derive(Clone, PartialEq)]
pub enum Expr {
    Tuple(TupleStyle, Vec<ExprS>),
    Ident(String),
    String(String),
    LString(String),
    XString(Vec<ExprS>),
    Exec(SubsMode, Box<ExprS>, Vec<ManOp>),
    Call(SubsMode, Box<ExprS>, Vec<ManOp>),
    Var(SubsMode, Box<ExprS>),
    Block(Vec<ExprS>),
    Lambda(Vec<(String, Option<ExprS>)>, Pat, RefCell<Option<Vec<ExprS>>>),
    Pipe(Vec<ExprS>, Option<Box<ExprS>>),
    Manip(ManOp, Box<ExprS>),
    Let(Pat, Box<ExprS>),
    Read(Vec<ExprS>),
    Set(SetOp, Box<ExprS>, Box<ExprS>),
    Import(ImportScope, Box<ExprS>, Option<Box<ExprS>>, Option<(SetOp, Box<ExprS>)>),
    And(Box<ExprS>, Box<ExprS>),
    Or(Box<ExprS>, Box<ExprS>),
    FuncDec(Pat, RefCell<Option<Vec<ExprS>>>),
    Background(Box<ExprS>),
    If{cond: Box<ExprS>, then: Vec<ExprS>, el: Option<Vec<ExprS>>},
    While{cond: Box<ExprS>, lo: Vec<ExprS>},
    For{pat: Pat, iter: Box<ExprS>, lo: Vec<ExprS>},
    Match{val: Box<ExprS>, cases: Vec<(Pat, ExprS)>},
    Index((String, Span), Box<ExprS>),
    Range(ASTRange),
    Break(Option<Box<ExprS>>),
    Continue(Option<Box<ExprS>>),
    Return(Option<Box<ExprS>>),
    Rex(RegexEq),
    Nop,
}

impl Deref for ExprS {
    type Target = Expr;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl ExprS {
    pub fn tuple(s: TupleStyle, v: Vec<ExprS>, sp: Span) -> ExprS {
        ExprS(Expr::Tuple(s, v), sp)
    }

    pub fn ident(s: String, sp: Span) -> ExprS {
        ExprS(Expr::Ident(s), sp)
    }

    pub fn string(s: String, sp: Span) -> ExprS {
        ExprS(Expr::String(s), sp)
    }

    pub fn lstring(s: String, sp: Span) -> ExprS {
        ExprS(Expr::LString(s), sp)
    }

    pub fn exec(m: SubsMode, e: ExprS, sp: Span) -> ExprS {
        ExprS(Expr::Exec(m, Box::new(e), vec![]), sp)
    }

    pub fn call(m: SubsMode, e: ExprS, sp: Span) -> ExprS {
        ExprS(Expr::Call(m, Box::new(e), vec![]), sp)
    }

    pub fn var(m: SubsMode, e: ExprS, sp: Span) -> ExprS {
        ExprS(Expr::Var(m, Box::new(e)), sp)
    }

    pub fn import(scope: ImportScope, name: ExprS, sp: Span) -> ExprS {
        ExprS(Expr::Import(scope, Box::new(name), None, None), sp)
    }

    pub fn import_as(scope: ImportScope,
                     name: ExprS,
                     name_as: ExprS,
                     sp: Span) -> ExprS {
        ExprS(Expr::Import(scope, Box::new(name),
                           Some(Box::new(name_as)), None), sp)
    }

    pub fn import_set(scope: ImportScope,
                      name: ExprS,
                      op: SetOp,
                      set: ExprS,
                      sp: Span) -> ExprS {
        ExprS(Expr::Import(scope, Box::new(name), None,
                           Some((op, Box::new(set)))), sp)
    }

    pub fn import_as_and_set(scope: ImportScope,
                             name: ExprS,
                             name_as: ExprS,
                             op: SetOp,
                             set: ExprS,
                             sp: Span) -> ExprS {
        ExprS(Expr::Import(scope, Box::new(name),
                           Some(Box::new(name_as)),
                           Some((op, Box::new(set)))), sp)
    }

    pub fn to_pat(e: ExprS) -> Res<Pat> {
        use self::Expr::*;
        use self::Pat::*;
        use self::ParseError::*;

        let span = e.1;
        match e.0 {
            Tuple(_, v) => {
                let mut ret = vec![];
                let mut iter = v.into_iter().map(|x| Self::to_pat(x));
                loop {
                    let p = iter.next();
                    match p {
                        Some(Ok(Wild(mut opt))) => {
                            //opt.extend(iter.filter(|p|
                               //match p { &Ok(Wild(..)) => false, _ => true}));
                            opt.reserve(iter.len());
                            for p in iter {
                                if let Ok(Wild(..)) = p {
                                    // Ignore "..." beyond first
                                } else {
                                    opt.push(p?)
                                }
                            }

                            ret.push(Wild(opt));
                            break;
                        },
                        Some(Ok(p)) => {
                            ret.push(p);
                        },
                        Some(Err(e)) => {
                            return Err(e);
                        },
                        None => break,
                    }
                }
                Ok(Tup(ret))
            }
            Ident(s) => Ok(ID(s)),
            String(s) | LString(s) => Ok(Str(s)),
            Range(self::ASTRange::All) => Ok(Wild(vec![])),
            Range(r) => Ok(Rng(ASTRange::from_ast_range(Cow::from(r))?)),
            Block(v) => {
                if let Some(v) = require_string_list(&v) {
                    Ok(StrList(v))
                } else if let Some((bind, expr)) = require_binding(v) {
                    Ok(Bind(bind.into(), Box::new(Self::to_pat(expr)?)))
                } else {
                    Err(InvalidPattern(ExprS(Nop, span), "{...} in pattern must contain a scalar list or an assignment"))
                }
            },
            Expr::Rex(r) => Ok(Pat::Rex(r)),
            _ => Err(InvalidPattern(e, "Invalid as pattern")),
        }
    }

    pub fn lambda_to_pat(binds: Vec<String>, e: ExprS) -> Res<Pat> {
        use ::std::sync::Mutex;
        use ::std::ops::Deref;
        lazy_static! { static ref LAMBDA_COUNT: Mutex<usize> = Mutex::new(0); }
        let name = if let Ok(mut l) = LAMBDA_COUNT.lock() {
            let name = Pat::Str(format!("@lambda{}@", l.deref()));
            *l += 1;
            name
        } else { panic!("Failed to take LAMBDA_COUNT mutex"); };

        let mut ret = Vec::with_capacity(1 + binds.len() + e.0.len());
        ret.push(name);
        ret.extend(binds.into_iter().map(|x| Pat::ID(x)));
        let pat = Self::to_pat(e)?;
        match pat {
            Pat::Tup(v) => ret.extend(v),
            _ => ret.push(pat),
        }
        //println!("Lambda pattern: {:?}", ret);
        Ok(Pat::Tup(ret))
    }

    pub fn is_callable(&self) -> bool {
        use self::Expr::*;
        match self.0 {
            Tuple(..) | Ident(..) | String(..) | LString(..) | XString(..) | Exec(..) | Call(..) | Var(..) | Lambda(..) => {
                true
            },
            _ => false
        }
    }
}

fn require_string_list(v: &Vec<ExprS>) -> Option<Vec<String>> {
    if v.len() != 1 { return None }
    let ref s = v[0].0;
    if let &Expr::Tuple(_, ref t) = s {
        let ret: Vec<Option<String>> = t.iter().map(|v| v.get_atom()).collect();
        if ret.iter().any(|v| v.is_none()) {
            return None
        } else {
            return Some(ret.into_iter().map(|v| v.unwrap()).collect())
        }
    } else {
        return None
    }
}

fn require_binding(mut v: Vec<ExprS>) -> Option<(String, ExprS)> {
    if v.len() != 1 { return None }
    let s: ExprS = v.drain(..).nth(0).unwrap();
    if let ExprS(Expr::Set(SetOp::Assign, lhs, rhs), _) = s {
        if let Some(id) = lhs.0.take_ident() {
            return Some((id, *rhs))
        } else {
            return None
        }
    } else {
        return None
    }
}

impl Expr {
    pub fn len(&self) -> usize {
        match self {
            &Expr::Tuple(_, ref v) => v.iter().fold(0, |acc, x| acc + x.len()),
            _ => 1,
        }
    }

    pub fn get_ident(&self) -> Option<&str> {
        if let &Expr::Ident(ref i) = self {
            Some(i)
        } else {
            None
        }
    }

    pub fn take_ident(self) -> Option<String> {
        if let Expr::Ident(i) = self {
            Some(i)
        } else {
            None
        }
    }

    pub fn take_block(self) -> Option<Vec<ExprS>> {
        if let Expr::Block(b) = self {
            Some(b)
        } else {
            None
        }
    }

    pub fn get_unquoted(&self) -> Option<String> {
        use ast::Expr::*;
        match self {
            &Ident(ref i) => Some(i.clone()),
            &String(ref i) => Some(i.clone()),
            _ => None,
        }
    }

    pub fn get_atom(&self) -> Option<String> {
        use ast::Expr::*;
        match self {
            &Ident(ref i) => Some(i.clone()),
            &String(ref i) => Some(i.clone()),
            &LString(ref i) => Some(i.clone()),
            _ => None,
        }
    }

    pub fn get_str_mut(&mut self) -> Option<&mut String> {
        use ast::Expr::*;
        match self {
            &mut String(ref mut i) => Some(i),
            &mut LString(ref mut i) => Some(i),
            _ => None,
        }
    }

    pub fn get_int(&self) -> Option<i64> {
        if let Some(s) = self.get_unquoted() {
            if let Ok(i) = str::parse::<i64>(s.as_str()) {
                Some(i)
            } else {
                None
            }
        } else {
            None
        }
    }

    pub fn get_1char(&self) -> Option<char> {
        if let Some(s) = self.get_atom() {
            let mut ret = None;
            for c in s.chars() {
                if ret == None {
                    ret = Some(c);
                } else {
                    return None;
                }
            }
            return ret;
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
}

impl fmt::Debug for Expr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use self::Expr::*;

        match self {
            &Ident(ref s) => write!(f, "{}", s),
            &String(ref s) => write!(f, "\"{}\"", s),
            &LString(ref s) => write!(f, "\'{}\'", s),
            &XString(ref s) => write!(f, "\"XString{:?}\"", s),
            &Exec(ref m, ref s, _) => write!(f, "Exec<{:#?}>{{{:#?}}}", m, s),
            &Call(ref m, ref s, _) => write!(f, "Call<{:#?}>{{{:#?}}}", m, s),
            &If{cond: ref c, then: ref t, el: ref e} => write!(f, "If({:#?}, {:#?}, {:#?})", c, t, e),
            &While{cond: ref c, lo: ref l} => write!(f, "While({:#?}, {:#?})", c, l),
            &For{pat: ref p, iter: ref i, lo: ref l} => write!(f, "For({:#?} in {:#?}, {:#?})", p, i, l),
            &Match{val: ref v, cases: ref c} => write!(f, "Match({:#?}){:#?}", v, c),
            &Var(ref m, ref s) => write!(f, "Var<{:#?}>{{{:#?}}}", m, s),
            &Block(ref r) => {
                //let Func{args: ref a, body: ref b} = *r.deref();
                write!(f, "{{{:#?}}}", r)
            },
            &Lambda(ref c, ref p, ref r) => {
                //let Func{args: ref a, body: ref b} = *r.deref();
                write!(f, "{{[{:#?}]|{:#?}| {:#?}}}", c, p, r.borrow())
            },
            &Pipe(ref p, ref q) => write!(f, "Pipe({:#?}, {:#?})", p, q),
            &Let(ref l, ref r) => write!(f, "Let({:#?} = {:#?})", l, r),
            &Read(ref p) => write!(f, "Read({:#?})", p),
            &Set(o, ref l, ref r) => write!(f, "{:#?}({:#?} = {:#?})", o, l, r),
            &Import(s, ref l, ref r, ref i) => write!(f, "Import({:#?} {:#?} : {:#?} = {:#?})", s, l, r, i),
            &Index(ref n, ref i) => write!(f, "Index({:#?}[{:#?}])", n, i),
            &And(ref l, ref r) => write!(f, "({:#?} && {:#?})", l, r),
            &Or(ref l, ref r) => write!(f, "({:#?} || {:#?})", l, r),
            &FuncDec(ref p, ref b) => write!(f, "fn {:#?} {:#?}", p, b),
            &Manip(ref m, ref e) => write!(f, "Manip({:#?}, {:#?})", m, e),
            &Background(ref s) => write!(f, "Background({:#?})", s),
            &Range(ref r) => write!(f, "Range({:#?})", r),
            &Break(ref e) => write!(f, "Break({:#?})", e),
            &Continue(ref e) => write!(f, "Continue({:#?})", e),
            &Return(ref e) => write!(f, "Return({:#?})", e),
            &Tuple(TupleStyle::Spaced, ref v) => {
                write!(f, "TupS{:#?}", v)
            }
            &Tuple(TupleStyle::Comma, ref v) => {
                write!(f, "TupC{:#?}", v)
            }
            &Tuple(TupleStyle::Named, ref v) => {
                write!(f, "{:#?}{:#?}", &v[0], &v[1..])
            }
            &Rex(RegexEq(ref r)) => {
                write!(f, "/{:?}/", r.as_str())
            }
            &Nop => write!(f, "Nop"),
        }
    }
}


