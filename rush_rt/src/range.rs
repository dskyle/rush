use val::{Val};
use error::{Res};
use std::clone::Clone;
use rush_pat::range::{Range, RangeHalf};
use std::ascii::AsciiExt;
use error::RuntimeError::*;

pub trait RangeExt {
    fn as_val(&self) -> Val;
    fn from_val_pair(l: &Val, r: &Val) -> Res<Range>;
    fn from_val(val: &Val) -> Res<Range>;
    fn contains_str(&self, o: &str) -> bool;
    fn enumerate(&self) -> Res<Val>;
    fn first(&self) -> Res<Val>;
    fn next(&self, cur: &Val) -> Res<Val>;
}

fn rng_open() -> Val {
    Val::Tup(vec![Val::str("Open")])
}

fn rng_int(i: i64) -> Val {
    Val::Tup(vec![Val::str("Int"), Val::Str(i.to_string())])
}

fn rng_ascii(c: u8) -> Val {
    Val::Tup(vec![Val::str("Ascii"), Val::Str((c as char).to_string())])
}

fn rng_str<T: Into<String>>(s: T) -> Val {
    Val::Tup(vec![Val::str("Str"), Val::Str(s.into())])
}

fn rng_val(l: Val, r: Val) -> Val {
    Val::Tup(vec![Val::str("Range"), l, r])
}

pub fn half_from_val(val: &Val) -> Res<RangeHalf> {
    use self::RangeHalf::*;

    let err = |msg: &'static str| {
        Err(InvalidRangeVal(Box::new(val.clone()), msg).into())
    };

    val.with_val(|val| {
        match val {
            &Val::Tup(ref v) => {
                if v.len() >= 1 {
                    v[0].with_val(|val| {
                        match val.get_str() {
                            Some("Open") => Ok(Open),
                            Some("Int") => {
                                if v.len() >= 2 {
                                    v[1].with_val(|val| {
                                        if let Some(s) = val.get_str() {
                                            if let Ok(i) = str::parse::<i64>(s) {
                                                Ok(Int(i))
                                            } else {
                                                err("Int(...) requires an integer argument")
                                            }
                                        } else {
                                            err("Int(...) argument must be a scalar string")
                                        }
                                    })
                                } else {
                                    err("Int(...) requires one argument")
                                }
                            },
                            Some("Ascii") => {
                                if v.len() >= 2 {
                                    v[1].with_val(|val| {
                                        if let Some(s) = val.get_str() {
                                            if let Some(c) = s.chars().nth(0) {
                                                if c.is_ascii() {
                                                    Ok(Ascii(c as u8))
                                                } else {
                                                    err("First char of Char(...) arg must be ASCII")
                                                }
                                            } else {
                                                err("Char(...) requires a non-empty string argument")
                                            }
                                        } else {
                                            err("Char(...) argument must be a scalar string")
                                        }
                                    })
                                } else {
                                    err("Char(...) requires one argument")
                                }
                            },
                            Some("Str") => {
                                if v.len() >= 2 {
                                    v[1].with_val(|val| {
                                        if let Some(s) = val.get_str() {
                                            Ok(Str(s.to_owned()))
                                        } else {
                                            err("Str(...) argument must be a scalar string")
                                        }
                                    })
                                } else {
                                    err("Str(...) requires one argument")
                                }
                            },
                            Some(..) | None => {
                                err("Range(...) arguments must be type Open, Int, or Ascii")
                            },
                        }
                    })
                } else {
                    err("Tuple arguments of Range(...) must be non-empty")
                }
            }
            _ => {
                err("Arguments of Range(...) must be tuples")
            }
        }
    })
}

impl RangeExt for Range {
    fn as_val(&self) -> Val {
        use self::Range::*;

        match self {
            &All => rng_val(rng_open(), rng_open()),
            &FromInt(i) => rng_val(rng_int(i), rng_open()),
            &TillInt(i) => rng_val(rng_open(), rng_int(i)),
            &WithinInt(l, r) => rng_val(rng_int(l), rng_int(r)),
            &FromAscii(c) => rng_val(rng_ascii(c), rng_open()),
            &TillAscii(c) => rng_val(rng_open(), rng_ascii(c)),
            &WithinAscii(l, r) => rng_val(rng_ascii(l), rng_ascii(r)),
            &FromStr(ref c) => rng_val(rng_str(c.to_owned()), rng_open()),
            &TillStr(ref c) => rng_val(rng_open(), rng_str(c.to_owned())),
            &WithinStr(ref l, ref r) => rng_val(rng_str(l.to_owned()), rng_str(r.to_owned())),
        }
    }


    fn from_val_pair(l: &Val, r: &Val) -> Res<Range> {
        use self::Range::*;
        use self::RangeHalf::*;

        match (half_from_val(l)?, half_from_val(r)?) {
            (Open, Open) => Ok(All),
            (Int(i), Open) => Ok(FromInt(i)),
            (Open, Int(i)) => Ok(TillInt(i)),
            (Int(l), Int(r)) => Ok(WithinInt(l, r)),
            (Ascii(i), Open) => Ok(FromAscii(i)),
            (Open, Ascii(i)) => Ok(TillAscii(i)),
            (Ascii(l), Ascii(r)) => Ok(WithinAscii(l, r)),
            (Str(i), Open) => Ok(FromStr(i)),
            (Open, Str(i)) => Ok(TillStr(i)),
            (Str(l), Str(r)) => Ok(WithinStr(l, r)),
            _ => Err(InvalidRangeVal(Box::new(Val::Tup(vec![l.clone(), r.clone()])), "Invalid arguments in Range(...)")),
        }
    }

    fn from_val(val: &Val) -> Res<Range> {
        match val {
            &Val::Tup(ref v) if v.len() == 3 && v[0].get_str().map(|v| v == "Range").unwrap_or(false) => {
                Self::from_val_pair(&v[1], &v[2])
            }
            _ => Err(InvalidRangeVal(Box::new(val.clone()), "Expected Range(_, _)")),
        }
    }

    fn contains_str(&self, o: &str) -> bool {
        use self::Range::*;

        match self {
            &All => true,
            &FromInt(i) =>
                if let Ok(v) = str::parse::<i64>(o) {
                    i <= v
                } else { false },
            &TillInt(i) =>
                if let Ok(v) = str::parse::<i64>(o) {
                    v <= i
                } else { false },
            &WithinInt(l, r) =>
                if let Ok(v) = str::parse::<i64>(o) {
                    (l <= v) && (v <= r)
                } else { false },
            &FromAscii(c) =>
                if o.is_ascii() {
                    o.bytes().nth(0).map(|v| c <= v).unwrap_or(false)
                } else { false },
            &TillAscii(c) =>
                if o.is_ascii() {
                    o.bytes().nth(0).map(|v| v <= c).unwrap_or(false)
                } else { false },
            &WithinAscii(l, r) =>
                if o.is_ascii() {
                    o.bytes().nth(0).map(|v| l <= v && v <= r).unwrap_or(false)
                } else { false },
            &FromStr(ref s) => o >= s.as_ref(),
            &TillStr(ref s) => o <= s.as_ref(),
            &WithinStr(ref l, ref r) => (o >= l.as_ref()) && (o <= r.as_ref()),
        }
    }

    fn first(&self) -> Res<Val> {
        use self::Val::*;
        match *self {
            Range::All => Err(InvalidRange(self.clone(), "Cannot iterate '..' range")),
            Range::WithinInt(f, _) | Range::FromInt(f) | Range::TillInt(f) =>
                Ok(Str(f.to_string())),
            Range::WithinAscii(f, _) | Range::FromAscii(f) | Range::TillAscii(f) =>
                Ok(Str((f as char).to_string())),
            Range::WithinStr(ref f, _) | Range::FromStr(ref f) | Range::TillStr(ref f)=>
                Ok(Str(f.clone())),
        }
    }

    fn next(&self, cur: &Val) -> Res<Val> {
        let ret = match *self {
            Range::All => Err(InvalidRange(self.clone(), "Cannot iterate '..' range")),
            Range::WithinStr(..) | Range::TillStr(..) | Range::FromStr(..) =>
                Err(InvalidRange(self.clone(), "Cannot iterate string ranges")),
            Range::WithinInt(f, t) => {
                let step = if f < t { 1 } else { -1 };
                next_int(cur, Some(t), step)
            },
            Range::FromInt(_) => next_int(cur, None, 1),
            Range::TillInt(_) => next_int(cur, None, -1),
            Range::WithinAscii(f, t) => {
                let step = if f < t { 1 } else { -1 };
                next_ascii(cur, Some(t), step)
            },
            Range::FromAscii(_) => next_ascii(cur, None, 1),
            Range::TillAscii(_) => next_ascii(cur, None, -1),
        };
        match ret {
            Ok(Some(v)) => Ok(Val::Str(v)),
            Ok(None) => Ok(Val::void()),
            Err(e) => Err(e),
        }
    }

    fn enumerate(&self) -> Res<Val> {
        use self::Val::*;

        match *self {
            Range::WithinInt(from, to) => {
                return Ok(Tup((from ..= to).map(|i| Str(i.to_string())).collect()));
            },
            Range::WithinAscii(from, to) => {
                let from = from as i16;
                let to = to as i16;
                return Ok(Tup((from ..= to).map(|i| Str((i as u8 as char).to_string())).collect()));
            },
            Range::WithinStr(..) => {
                return Err(InvalidRange(self.clone(), "Attempted to enumerate string range (only integer or char ranges allowed)"));
            },
            _ => {
                return Err(InvalidRange(self.clone(), "Attempted to enumerate unbounded range"));
            },
        }
    }
}

fn expect_ascii(s: &str) -> Option<u8> {
    if s.len() == 1 {
        if let Some(s) = s.chars().nth(0) {
            if s.is_ascii() {
                return Some(s as u8)
            }
        }
    }
    return None
}

fn next_int(val: &Val, last: Option<i64>, step: i64) -> Res<Option<String>> {
    if let Some(cur) = val.get_str() {
        if let Ok(cur) = str::parse::<i64>(cur) {
            let cur = cur + step;
            if last.is_some() && cur * step > last.unwrap() * step {
                Ok(None)
            } else {
                Ok(Some(cur.to_string()))
            }
        } else {
            Err(BadValType(Box::new(val.clone()), "Expected parseable integer"))
        }
    } else {
        Err(BadValType(Box::new(val.clone()), "Expected scalar string"))
    }
}

fn next_ascii(val: &Val, last: Option<u8>, step: i8) -> Res<Option<String>> {
    if let Some(cur) = val.get_str() {
        if let Some(cur) = expect_ascii(cur) {
            let cur = ((cur as i16) + (step as i16)) as u8;
            if last.is_some() && (cur as i16) * (step as i16) > (last.unwrap() as i16) * (step as i16) {
                Ok(None)
            } else {
                Ok(Some((cur as char).to_string()))
            }
        } else {
            Err(BadValType(Box::new(val.clone()), "Expected single ascii character"))
        }
    } else {
        Err(BadValType(Box::new(val.clone()), "Expected scalar string"))
    }
}
