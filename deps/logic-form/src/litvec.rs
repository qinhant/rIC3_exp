use crate::{Lit, Var};
use giputils::hash::GHashSet;
use std::{
    cmp::Ordering,
    collections::BTreeMap,
    fmt::{self, Debug, Display},
    ops::{Deref, DerefMut, Not},
    slice,
};
use var2name::var2info;

#[derive(Clone, Hash, PartialEq, Eq)]
pub struct LitVec {
    lits: Vec<Lit>,
}

impl LitVec {
    #[inline]
    pub fn new() -> Self {
        LitVec { lits: Vec::new() }
    }

   

    #[inline]
    pub fn new_with(c: usize) -> Self {
        LitVec {
            lits: Vec::with_capacity(c),
        }
    }
    #[inline]
    pub fn new_from_slice(slice: &[Lit]) -> Self {
        LitVec {
            lits: Vec::from(slice),
        }
    }

    #[inline]
    pub fn last(&self) -> Lit {
        #[cfg(debug_assertions)]
        {
            self.lits.last().copied().unwrap()
        }
        #[cfg(not(debug_assertions))]
        unsafe {
            self.lits.last().copied().unwrap_unchecked()
        }
    }

    #[inline]
    pub fn cls_simp(&mut self) {
        self.sort();
        self.dedup();
        for i in 1..self.len() {
            if self[i] == !self[i - 1] {
                self.clear();
                return;
            }
        }
    }

    #[inline]
    pub fn subsume(&self, o: &[Lit]) -> bool {
        if self.len() > o.len() {
            return false;
        }
        'n: for x in self.iter() {
            for y in o.iter() {
                if x == y {
                    continue 'n;
                }
            }
            return false;
        }
        true
    }

    pub fn subsume_execpt_one(&self, o: &[Lit]) -> (bool, Option<Lit>) {
        if self.len() > o.len() {
            return (false, None);
        }
        let mut diff = None;
        'n: for x in self.iter() {
            for y in o.iter() {
                if x == y {
                    continue 'n;
                }
                if diff.is_none() && x.var() == y.var() {
                    diff = Some(*x);
                    continue 'n;
                }
            }
            return (false, None);
        }

        (diff.is_none(), diff)
    }

    #[inline]
    pub fn ordered_subsume(&self, cube: &LitVec) -> bool {
        debug_assert!(self.is_sorted());
        debug_assert!(cube.is_sorted());
        if self.len() > cube.len() {
            return false;
        }
        let mut j = 0;
        for i in 0..self.len() {
            while j < cube.len() && self[i].0 > cube[j].0 {
                j += 1;
            }
            if j == cube.len() || self[i] != cube[j] {
                return false;
            }
        }
        true
    }

    #[inline]
    pub fn ordered_subsume_execpt_one(&self, cube: &LitVec) -> (bool, Option<Lit>) {
        debug_assert!(self.is_sorted());
        debug_assert!(cube.is_sorted());
        let mut diff = None;
        if self.len() > cube.len() {
            return (false, None);
        }
        let mut j = 0;
        for i in 0..self.len() {
            while j < cube.len() && self[i].var() > cube[j].var() {
                j += 1;
            }
            if j == cube.len() {
                return (false, None);
            }
            if self[i] != cube[j] {
                if diff.is_none() && self[i].var() == cube[j].var() {
                    diff = Some(self[i]);
                } else {
                    return (false, None);
                }
            }
        }
        (diff.is_none(), diff)
    }

    #[inline]
    pub fn intersection(&self, cube: &LitVec) -> LitVec {
        let x_lit_set = self.iter().collect::<GHashSet<&Lit>>();
        let y_lit_set = cube.iter().collect::<GHashSet<&Lit>>();
        Self {
            lits: x_lit_set
                .intersection(&y_lit_set)
                .copied()
                .copied()
                .collect(),
        }
    }

    #[inline]
    pub fn ordered_intersection(&self, cube: &LitVec) -> LitVec {
        debug_assert!(self.is_sorted());
        debug_assert!(cube.is_sorted());
        let mut res = LitVec::new();
        let mut i = 0;
        for l in self.iter() {
            while i < cube.len() && cube[i] < *l {
                i += 1;
            }
            if i == cube.len() {
                break;
            }
            if *l == cube[i] {
                res.push(*l);
            }
        }
        res
    }

    #[inline]
    pub fn resolvent(&self, other: &LitVec, v: Var) -> Option<LitVec> {
        let (x, y) = if self.len() < other.len() {
            (self, other)
        } else {
            (other, self)
        };
        let mut new = LitVec::new();
        'n: for x in x.iter() {
            if x.var() != v {
                for y in y.iter() {
                    if x.var() == y.var() {
                        if *x == !*y {
                            return None;
                        } else {
                            continue 'n;
                        }
                    }
                }
                new.push(*x);
            }
        }
        new.extend(y.iter().filter(|l| l.var() != v).copied());
        Some(new)
    }

    #[inline]
    pub fn ordered_resolvent(&self, other: &LitVec, v: Var) -> Option<LitVec> {
        debug_assert!(self.is_sorted());
        debug_assert!(other.is_sorted());
        let (x, y) = if self.len() < other.len() {
            (self, other)
        } else {
            (other, self)
        };
        let mut new = LitVec::new_with(self.len() + other.len());
        let (mut i, mut j) = (0, 0);
        while i < x.len() {
            if x[i].var() == v {
                i += 1;
                continue;
            }
            while j < y.len() && y[j].var() < x[i].var() {
                j += 1;
            }
            if j < y.len() && x[i].var() == y[j].var() {
                if x[i] == !y[j] {
                    return None;
                }
            } else {
                new.push(x[i]);
            }
            i += 1;
        }
        new.extend(y.iter().filter(|l| l.var() != v).copied());
        Some(new)
    }

    #[inline]
    pub fn map(&self, f: impl Fn(Lit) -> Lit) -> LitVec {
        let mut new = LitVec::new_with(self.len());
        for l in self.iter() {
            new.push(f(*l));
        }
        new
    }

}

impl Default for LitVec {
    fn default() -> Self {
        Self::new()
    }
}

impl Deref for LitVec {
    type Target = Vec<Lit>;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.lits
    }
}

impl DerefMut for LitVec {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.lits
    }
}

impl PartialOrd for LitVec {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for LitVec {
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        debug_assert!(self.is_sorted());
        debug_assert!(other.is_sorted());
        let min_index = self.len().min(other.len());
        for i in 0..min_index {
            match self[i].0.cmp(&other[i].0) {
                Ordering::Less => return Ordering::Less,
                Ordering::Equal => {}
                Ordering::Greater => return Ordering::Greater,
            }
        }
        self.len().cmp(&other.len())
    }
}

impl Not for LitVec {
    type Output = LitVec;

    #[inline]
    fn not(self) -> Self::Output {
        let lits = self.lits.iter().map(|lit| !*lit).collect();
        LitVec { lits }
    }
}

impl Not for &LitVec {
    type Output = LitVec;

    #[inline]
    fn not(self) -> Self::Output {
        let lits = self.lits.iter().map(|lit| !*lit).collect();
        LitVec { lits }
    }
}

impl<const N: usize> From<[Lit; N]> for LitVec {
    #[inline]
    fn from(s: [Lit; N]) -> Self {
        Self { lits: Vec::from(s) }
    }
}

impl From<Lit> for LitVec {
    #[inline]
    fn from(l: Lit) -> Self {
        Self { lits: vec![l] }
    }
}

impl From<&[Lit]> for LitVec {
    #[inline]
    fn from(s: &[Lit]) -> Self {
        Self { lits: Vec::from(s) }
    }
}

impl From<LitVec> for Vec<Lit> {
    #[inline]
    fn from(val: LitVec) -> Self {
        val.lits
    }
}

impl FromIterator<Lit> for LitVec {
    #[inline]
    fn from_iter<T: IntoIterator<Item = Lit>>(iter: T) -> Self {
        Self {
            lits: Vec::from_iter(iter),
        }
    }
}

impl IntoIterator for LitVec {
    type Item = Lit;
    type IntoIter = std::vec::IntoIter<Lit>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.lits.into_iter()
    }
}

impl<'a> IntoIterator for &'a LitVec {
    type Item = &'a Lit;
    type IntoIter = slice::Iter<'a, Lit>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.lits.iter()
    }
}

impl AsRef<[Lit]> for LitVec {
    #[inline]
    fn as_ref(&self) -> &[Lit] {
        self.as_slice()
    }
}

impl Display for LitVec {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[")?;
        struct Value {
            pub known_mask: u64,
            pub value: u64,
            pub lits: Vec<Lit>,
        }
        let mut data = BTreeMap::<String, Value>::new();
        let mut wrote = false;
        let mut write_comma = |f: &mut fmt::Formatter<'_>| {
            if wrote {
                write!(f, ", ")?;
            } else {
                wrote = true;
            }
            Ok(())
        };
        let mut write_wrap = |info: &Lit| {
            write_comma(f)?;
            write!(f, "{}", info)
        };
        for lit in &self.lits {
            let Some(info) = var2info(lit.var().into()) else {
                write_wrap(&lit)?;
                continue;
            };
            if !info.is_vector {
                write_wrap(&lit)?;
                continue;
            }
            let entry = data.entry(info.name).or_insert(Value {
                known_mask: 0,
                value: 0,
                lits: Vec::new(),
            });
            entry.known_mask |= (1 as u64) << info.index;
            entry.value |= (lit.polarity() as u64) << info.index;
            entry.lits.push(*lit);
        }
        for (name, entry) in data {
            write_comma(f)?;
            if entry.lits.len() == 1 {
                write!(f, "{}", entry.lits[0])?;
                continue;
            }
            let max_index = 63 - entry.known_mask.leading_zeros();
            let min_index = entry.known_mask.trailing_zeros();
            let val = entry.value >> min_index;
            let all_known = (min_index..(max_index + 1)).all(|i| entry.known_mask & (1 << i) != 0);
            if all_known {
                write!(f, "{}[{}:{}]={:x}", name, max_index, min_index, val)?;
                continue;
            }
            write!(f, "{}[{}:{}]=", name, max_index, min_index)?;
            for i in (min_index..(max_index + 1)).rev() {
                write!(
                    f,
                    "{}",
                    if entry.known_mask & (1 << i) != 0 {
                        if ((val >> i) & 1) != 0 { "1" } else { "0" }
                    } else {
                        "x"
                    }
                )?;
            }
        }
        return write!(f, "]");
    }
}

impl Debug for LitVec {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Display::fmt(&self, f)
    }
}
