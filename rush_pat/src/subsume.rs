use std::ops::{BitAnd, BitAndAssign};
use std::clone::Clone;
use regex::Regex;

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum Subsumption {
    Disjoint,
    Contains,
    Same,
    Overlaps,
    ContainedBy,
}

impl Subsumption {
    pub fn reverse(self) -> Subsumption {
        use self::Subsumption::*;

        match self {
            Disjoint => Disjoint,
            Contains => ContainedBy,
            Same => Same,
            Overlaps => Overlaps,
            ContainedBy => Contains,
        }
    }

    pub fn same_or_contains(self) -> bool {
        use self::Subsumption::*;

        return self == Same || self == Contains
    }

    pub fn same_or_contained_by(self) -> bool {
        use self::Subsumption::*;

        return self == Same || self == ContainedBy
    }
}

impl BitAndAssign for Subsumption {
    fn bitand_assign(&mut self, rhs: Self) {
        use self::Subsumption::*;
        *self = match (*self, rhs) {
            (Disjoint, _) | (_, Disjoint) => Disjoint,
            (Same, Same) => Same,
            (Same, x) | (x, Same) => x,
            (Overlaps, _) | (_, Overlaps) | (Contains, ContainedBy) | (ContainedBy, Contains) => Overlaps,
            (Contains, Contains) => Contains,
            (ContainedBy, ContainedBy) => ContainedBy,
        }
    }
}

impl BitAnd for Subsumption {
    type Output = Subsumption;

    fn bitand(self, rhs: Self) -> Self::Output {
        let mut ret = self.clone();
        ret.bitand_assign(rhs);
        ret
    }
}

pub trait Subsumes<RHS = Self> where RHS: ?Sized {
    fn subsumes(&self, other: &RHS) -> Subsumption;
}

pub trait IterOps<T, I>: IntoIterator<Item = T>
    where I: IntoIterator<Item = T>,
          T: PartialEq {
    fn intersect(self, other: I) -> Vec<T>;
    fn difference(self, other: I) -> Vec<T>;
}

impl Subsumes<str> for str {
    fn subsumes(&self, ss: &str) -> Subsumption {
        use self::Subsumption::*;

        if self == ss {
            Same
        } else {
            Disjoint
        }
    }
}

impl Subsumes<str> for Vec<String> {
    fn subsumes(&self, ss: &str) -> Subsumption {
        use self::Subsumption::*;

        if self.iter().any(|os| ss == os) {
            Contains
        } else {
            Disjoint
        }
    }
}

impl Subsumes<Vec<String>> for str {
    fn subsumes(&self, v: &Vec<String>) -> Subsumption {
        v.subsumes(self).reverse()
    }
}

fn intersect<T, I>(this: I, other: I) -> Vec<T> where I: IntoIterator<Item = T>, T: PartialEq {
    let mut common = Vec::new();
    let mut v_other: Vec<_> = other.into_iter().collect();

    for e1 in this.into_iter() {
        if let Some(pos) = v_other.iter().position(|e2| e1 == *e2) {
            common.push(e1);
            v_other.remove(pos);
        }
    }

    common
}

impl Subsumes for Vec<String> {
    fn subsumes(&self, o: &Self) -> Subsumption {
        use self::Subsumption::*;

        let inter = intersect(self.iter(), o.iter());
        if inter.len() == 0 {
            Disjoint
        } else {
            match (inter.len() == self.len(), inter.len() == o.len()) {
                (true, true) => Same,
                (false, false) => Overlaps,
                (true, false) => ContainedBy,
                (false, true) => ContainedBy,
            }
        }
    }
}

impl Subsumes<Regex> for str {
    fn subsumes(&self, rex: &Regex) -> Subsumption {
        use self::Subsumption::*;

        if rex.is_match(self) {
            ContainedBy
        } else {
            Disjoint
        }
    }
}

impl Subsumes<str> for Regex {
    fn subsumes(&self, s: &str) -> Subsumption {
        s.subsumes(self).reverse()
    }
}

impl Subsumes<Regex> for Vec<String> {
    fn subsumes(&self, rex: &Regex) -> Subsumption {
        use self::Subsumption::*;

        let count = self.iter().fold(0, |acc, x| acc + if rex.is_match(x) { 1 } else { 0 });
        if count == 0 {
            Disjoint
        } else if count == self.len() {
            ContainedBy
        } else {
            Overlaps
        }
    }
}

impl Subsumes<Vec<String>> for Regex {
    fn subsumes(&self, v: &Vec<String>) -> Subsumption {
        v.subsumes(self).reverse()
    }
}


