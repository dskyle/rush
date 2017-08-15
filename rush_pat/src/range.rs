use std::clone::Clone;
use subsume::{Subsumption, Subsumes};
use std::ascii::AsciiExt;
use std::fmt::{Display, Formatter, Error};
use std::borrow::Cow;
use self::Cow::*;

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub enum Range {
    All,
    FromAscii(u8),
    TillAscii(u8),
    WithinAscii(u8, u8),
    FromInt(i64),
    TillInt(i64),
    WithinInt(i64, i64),
    FromStr(String),
    TillStr(String),
    WithinStr(String, String),
}

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub enum RangeHalf {
    Open,
    Int(i64),
    Ascii(u8),
    Str(String),
}

impl Range {
    pub fn contains_str(&self, o: &str) -> bool {
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

    pub fn to_string(&self) -> String {
        format!("{}", self)
    }

    pub fn to_str_range(&self) -> Range {
        use self::Range::*;

        match self {
            &FromInt(i) => FromStr(i.to_string()),
            &TillInt(i) => TillStr(i64_to_maxwidth_string(i)),
            &WithinInt(l, r) => WithinStr(l.to_string(), i64_to_maxwidth_string(r)),
            &FromAscii(c) =>  FromStr((c as char).to_string()),
            &TillAscii(c) => TillStr((c as char).to_string()),
            &WithinAscii(l, r) => WithinStr((l as char).to_string(), (r as char).to_string()),
            _ => self.clone(),
        }
    }
}

fn i64_to_maxwidth_string(t: i64) -> String {
    format!("{:020}", t)
}

impl Display for Range {
    fn fmt(&self, f: &mut Formatter) -> Result<(), Error> {
        use self::Range::*;

        match self {
            &All => write!(f, "..."),
            &FromInt(i) => write!(f, "{}...", i),
            &TillInt(i) => write!(f, "...{}", i),
            &WithinInt(l, r) => write!(f, "{}...{}", l, r),
            &FromAscii(c) => write!(f, "{}...", c),
            &TillAscii(c) => write!(f, "...{}", c),
            &WithinAscii(l, r) => write!(f, "{}...{}", l, r),
            &FromStr(ref c) => write!(f, "{}...", c),
            &TillStr(ref c) => write!(f, "...{}", c),
            &WithinStr(ref l, ref r) => write!(f, "{}...{}", l, r),
        }
    }
}

impl<'a> From<Range> for Cow<'a, Range> {
    fn from(v: Range) -> Self {
        Owned(v)
    }
}

impl<'a> From<&'a Range> for Cow<'a, Range> {
    fn from(v: &'a Range) -> Self {
        Borrowed(v)
    }
}


impl Subsumes<str> for Range {
    fn subsumes(&self, x: &str) -> Subsumption {
        x.subsumes(self).reverse()
    }
}

impl Subsumes<Range> for str {
    fn subsumes(&self, rng: &Range) -> Subsumption {
        if rng.contains_str(self) {
            Subsumption::ContainedBy
        } else {
            Subsumption::Disjoint
        }
    }
}

impl Subsumes<Range> for Vec<String> {
    fn subsumes(&self, rng: &Range) -> Subsumption {
        use self::Subsumption::*;

        let count = self.iter().fold(0, |acc, x| acc + if rng.contains_str(x) { 1 } else { 0 });
        if count == 0 {
            Disjoint
        } else if count == self.len() {
            ContainedBy
        } else {
            Overlaps
        }
    }
}

impl Subsumes<Vec<String>> for Range {
    fn subsumes(&self, x: &Vec<String>) -> Subsumption {
        x.subsumes(self).reverse()
    }
}

fn reorder<T>(p: (T, T)) -> (T, T) where T: PartialOrd {
    if p.0 > p.1 { (p.1, p.0) } else { p }
}

pub fn lexical_int_range(mut low: i64, mut high: i64) -> (String, String) {
    let mut neg = 0;
    let mut sign = 1;
    if low < 0 && high < 0 {
        ::std::mem::swap(&mut low, &mut high);
        neg = 1;
        sign = -1;
    }
    let mut l = low.to_string().into_bytes();
    let mut h = high.to_string().into_bytes();
    if low < 0 && high >= 0 {
        l = "-1".to_string().into_bytes()
    } else {
        let val = sign * 10i64.pow(l.len() as u32 - neg);
        if sign * val <= high {
            l = val.to_string().into_bytes()
        }
    }
    if h.len() > 1 + neg as usize {
        let val = sign * (10i64.pow(h.len() as u32 - 1) - 1);
        if sign * val >= low {
            h = val.to_string().into_bytes();
        }
    }
    unsafe {
        (String::from_utf8_unchecked(l), String::from_utf8_unchecked(h))
    }
}

fn pairs_int_str_subsumes(l: (i64, i64), r: (&str, &str)) -> Subsumption {
    let l = reorder(l);
    let r = reorder(r);

    use self::Subsumption::*;

    if let (Some(a), Some(b)) = (int_to_ascii(l.0), int_to_ascii(l.1)) {
        return pairs_subsumes(((a as char).to_string().as_ref(), (b as char).to_string().as_ref()), r)
    }

    let l = lexical_int_range(l.0, l.1);

    pairs_subsumes((l.0.as_ref(), l.1.as_ref()), r) & Overlaps
}

fn pairs_subsumes<T>(l: (T, T), r: (T, T)) -> Subsumption where T: PartialOrd+::std::fmt::Debug {
    let l = reorder(l);
    let r = reorder(r);

    use self::Subsumption::*;

    if l.0 == r.0 && l.1 == r.1 {
        Same
    } else if l.0 <= r.0 && l.1 >= r.1 {
        Contains
    } else if r.0 <= l.0 && r.1 >= l.1 {
        ContainedBy
    } else if l.1 < r.0 || r.1 < l.0 {
        Disjoint
    } else {
        Overlaps
    }
}

fn pair_from_subsumes<T>(l: (T, T), r: T) -> Subsumption where T: PartialOrd {
    let l = reorder(l);

    use self::Subsumption::*;

    if r <= l.0 {
        ContainedBy
    } else if r > l.1 {
        Disjoint
    } else {
        Overlaps
    }
}

fn pair_till_subsumes<T>(l: (T, T), r: T) -> Subsumption where T: PartialOrd {
    let l = reorder(l);

    use self::Subsumption::*;

    if r >= l.1 {
        ContainedBy
    } else if r < l.0 {
        Disjoint
    } else {
        Overlaps
    }
}

fn from_subsumes<T>(l: T, r: T) -> Subsumption where T: PartialOrd {
    use self::Subsumption::*;

    if l == r {
        Same
    } else if l > r {
        Contains
    } else {
        ContainedBy
    }
}

fn till_subsumes<T>(l: T, r: T) -> Subsumption where T: PartialOrd {
    use self::Subsumption::*;

    if l == r {
        Same
    } else if l > r {
        ContainedBy
    } else {
        Contains
    }
}

fn int_to_ascii(i: i64) -> Option<u8> {
    if i >= 0 && i <= 9 {
        Some('0' as u8 + (i as u8))
    } else {
        None
    }
}

impl Subsumes for Range {
    fn subsumes(&self, other: &Self) -> Subsumption {
        use self::Range::*;
        use self::Subsumption::*;

        //println!("subsumes {:?} {:?}", self, other);
        match (self, other) {
            (&WithinInt(lb, lt), &WithinInt(rb, rt)) => pairs_subsumes((lb, lt), (rb, rt)),
            (&WithinInt(lb, lt), &FromInt(r)) => pair_from_subsumes((lb, lt), r),
            (&WithinInt(lb, lt), &TillInt(r)) => pair_till_subsumes((lb, lt), r),
            (&TillInt(l), &TillInt(r)) => till_subsumes(l, r),
            (&TillInt(l), &FromInt(r)) => if l < r { Disjoint } else { Overlaps },
            (&FromInt(l), &FromInt(r)) => from_subsumes(l, r),

            (&WithinAscii(lb, lt), &WithinAscii(rb, rt)) => pairs_subsumes((lb, lt), (rb, rt)),
            (&WithinAscii(lb, lt), &FromAscii(r)) => pair_from_subsumes((lb, lt), r),
            (&WithinAscii(lb, lt), &TillAscii(r)) => pair_till_subsumes((lb, lt), r),
            (&TillAscii(l), &TillAscii(r)) => till_subsumes(l, r),
            (&TillAscii(l), &FromAscii(r)) => if l < r { Disjoint } else { Overlaps },
            (&FromAscii(l), &FromAscii(r)) => from_subsumes(l, r),

            (&WithinStr(ref lb, ref lt), &WithinStr(ref rb, ref rt)) => pairs_subsumes((lb, lt), (rb, rt)),
            (&WithinStr(ref lb, ref lt), &FromStr(ref r)) => pair_from_subsumes((lb, lt), r),
            (&WithinStr(ref lb, ref lt), &TillStr(ref r)) => pair_till_subsumes((lb, lt), r),
            (&TillStr(ref l), &TillStr(ref r)) => till_subsumes(l, r),
            (&TillStr(ref l), &FromStr(ref r)) => if l < r { Disjoint } else { Overlaps },
            (&FromStr(ref l), &FromStr(ref r)) => from_subsumes(l, r),

            (&WithinInt(lb, lt), &WithinStr(ref rb, ref rt)) => pairs_int_str_subsumes((lb, lt), (rb, rt)),
            (&WithinInt(lb, lt), &FromStr(ref r)) => pairs_int_str_subsumes((lb, lt), (r, "~")),
            (&WithinInt(lb, lt), &TillStr(ref r)) => pairs_int_str_subsumes((lb, lt), ("!", r)),

            (&FromInt(l), &WithinStr(ref rb, ref rt)) => pairs_int_str_subsumes((l, i64::max_value() / 100), (rb, rt)),
            (&FromInt(l), &FromStr(ref r)) => pairs_int_str_subsumes((l, i64::max_value() / 100), (r, "~")),
            (&FromInt(l), &TillStr(ref r)) => pairs_int_str_subsumes((l, i64::max_value() / 100), ("!", r)),

            (&TillInt(l), &WithinStr(ref rb, ref rt)) => pairs_int_str_subsumes((i64::min_value() / 100, l), (rb, rt)),
            (&TillInt(l), &FromStr(ref r)) => pairs_int_str_subsumes((i64::min_value() / 100, l), (r, "~")),
            (&TillInt(l), &TillStr(ref r)) => pairs_int_str_subsumes((i64::min_value() / 100, l), ("!", r)),

            (l @ &WithinAscii(..), r) => l.to_str_range().subsumes(r),
            (l, r @ &WithinAscii(..)) => l.subsumes(&r.to_str_range()),
            (l @ &FromAscii(..), r) => l.to_str_range().subsumes(r),
            (l, r @ &FromAscii(..)) => l.subsumes(&r.to_str_range()),
            (l @ &TillAscii(..), r) => l.to_str_range().subsumes(r),
            (l, r @ &TillAscii(..)) => l.subsumes(&r.to_str_range()),

            (&All, &All) => Same,
            (&All, _) => Contains,
            (_,&All) => ContainedBy,

            (l, r) => r.subsumes(l).reverse(),
        }
    }
}
