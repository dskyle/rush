use regex::Regex;
use subsume::{Subsumes, Subsumption};
use range::{Range};

#[derive(Debug, Clone)]
pub struct RegexEq(pub Regex);

#[derive(Debug, Clone, PartialEq)]
pub enum Pat {
    Tup(Vec<Pat>),
    ID(String),
    Str(String),
    StrList(Vec<String>),
    Wild(Vec<Pat>),
    Bind(String, Box<Pat>),
    Rng(Range),
    Rex(RegexEq),
}

impl Pat {
    pub fn get_id(&self) -> Option<&str> {
        use self::Pat::*;
        match *self {
            ID(ref s) => Some(s),
            _ => None,
        }
    }

    pub fn get_str(&self) -> Option<&str> {
        use self::Pat::*;
        match *self {
            Str(ref s) => Some(s),
            _ => None,
        }
    }

    pub fn get_atom(&self) -> Option<&str> {
        use self::Pat::*;
        match *self {
            ID(ref s) | Str(ref s) => Some(s),
            _ => None,
        }
    }

    pub fn is_wild(&self) -> bool {
        match *self {
            Pat::Wild(_) => true,
            _ => false,
        }
    }

    pub fn has_wild(&self) -> bool {
        match *self {
            Pat::Wild(_) => true,
            Pat::Tup(ref v) => {
                if let Some(&Pat::Wild(_)) = v.last() { true } else { false }
            },
            Pat::Bind(_, ref p) => p.has_wild(),
            _ => false,
        }
    }

    pub fn len(&self) -> usize {
        match *self {
            Pat::Tup(ref v) => v.len(),
            Pat::Bind(_, ref p) => p.len(),
            _ => 1,
        }
    }

    pub fn req_len(&self) -> usize {
        match *self {
            Pat::Tup(ref v) => {
                v.len() - if self.has_wild() { 1 } else { 0 }
            },
            Pat::Bind(_, ref p) => p.req_len(),
            Pat::Wild(..) => 0,
            _ => 1,
        }
    }
}

impl PartialEq for RegexEq {
    fn eq(&self, other: &Self) -> bool {
        self.0.as_str() == other.0.as_str()
    }
}

impl Subsumes for Vec<Pat> {
    fn subsumes(&self, ov: &Self) -> Subsumption {
        use self::Subsumption::*;
        use self::Pat::*;

        let mut l = self.iter();
        let mut r = ov.iter();
        let mut ret = Same;
        loop {
            let lv = l.next();
            let rv = r.next();
            //println!("Iterate: {:?} ?? {:?}   ({:?})", lv, rv, ret);

            match (lv, rv) {
                (None, None) | (Some(&Wild(..)), None) | (None, Some(&Wild(..))) | (Some(&Wild(..)), Some(&Wild(..))) => return ret,
                (None, _) | (_, None) => return Disjoint,
                (Some(&Wild(..)), _) => return ret & Contains,
                (_, Some(&Wild(..))) => return ret & ContainedBy,
                (Some(lv), Some(rv)) => {
                    let sub = lv.subsumes(rv);
                    //println!("{:?} & {:?} {:?} {:?}", ret, lv, sub, rv);
                    ret &= sub;
                },
            }
        }
    }
}

impl Subsumes for Pat {
    fn subsumes(&self, other: &Pat) -> Subsumption {
        use self::Subsumption::*;
        use self::Pat::*;

        //println!("{:?} ?? {:?}", self, other);
        match (self, other) {
            (&Bind(_, ref sp), &Bind(_, ref op)) => (*sp).subsumes(&**op),
            (_, &Bind(_, ref op)) => self.subsumes(&**op),
            (&Bind(_, ref sp), _) => sp.subsumes(other),

            (&Wild(..), &Wild(..)) => Same,
            (&Wild(..), _) => Contains,
            (_, &Wild(..)) => ContainedBy,

            (&ID(_), &ID(_)) => Same,
            (&ID(_), _) => Contains,
            (_, &ID(_)) => ContainedBy,

            (&Str(ref ss), &Str(ref os)) => if ss == os { Same } else { Disjoint },
            (&Str(ref ss), &StrList(ref ol)) => ss.subsumes(ol),
            (&Str(ref ss), &Rng(ref or)) => ss.subsumes(or),
            (&Str(ref ss), &Rex(ref or)) => ss.subsumes(&or.0),

            (&StrList(ref sl), &StrList(ref ol)) => sl.subsumes(ol),

            (&StrList(ref sl), &Rng(ref or)) => sl.subsumes(or),
            (&StrList(ref sl), &Rex(ref or)) => sl.subsumes(&or.0),
            (&StrList(_), _) => other.subsumes(self).reverse(),

            (&Rng(ref sr), &Rng(ref or)) => sr.subsumes(or),
            (&Rng(ref _sr), &Rex(ref _or)) => Overlaps, // TODO
            (&Rng(_), _) => other.subsumes(self).reverse(),

            (&Rex(ref _sr), &Rex(ref _or)) => Overlaps, // TODO
            (&Rex(_), _) => other.subsumes(self).reverse(),

            (&Tup(ref sv), &Tup(ref ov)) => { sv.subsumes(ov) },

            //(&Tup(ref sv), _) => if sv.len() == 1 { sv[0].subsumes(other) } else { Disjoint },
            (&Tup(_), _) => Disjoint,
            (_, &Tup(_)) => other.subsumes(self).reverse(),
        }
    }
}

#[macro_export]
macro_rules! mk_pat {
    ( ($($x:tt),*) ) => ( Pat::Tup(vec![$(mk_pat!($x)),*]) );
    ( [$($x:tt),*] ) => ( Pat::Wild(vec![$(mk_pat!($x)),*]) );
    ( ... ) => ( Pat::Wild(vec![]) );
    ( {$x:ident = $y:tt} ) => ( Pat::Bind(stringify!($x).to_string(), Box::new(mk_pat!($y))) );
    ( {$x:ident} ) => ( Pat::ID(stringify!($x).to_string()) );
    ( $x:tt ) => ( Pat::Str(stringify!($x).trim_matches('"').to_string()) );
}
