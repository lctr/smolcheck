use std::borrow::Cow;

use lexicon::{Lexicon, Sym};

use crate::Hashy;

extern crate lexicon;

/// For greater efficiency, identifiers (outside of the scope of this toy
/// crate) should be interned, as it would mean passing around "interner
/// keys", which should be more lightweight assuming the interner key
/// (denoted `SymId` here) has a smaller size than a `String` or a string
/// slice. The `SymId` type, while a simple type alias here, should
/// ultimately be a `newtype` for string interner keys.
///
/// For a simple string interner, we may assume that static string slices
/// are stored and retrieved via a key -- in this case, since this toy
/// crate doesn't include an actual string interner, the mere skeleton is
/// included for completeness' sake.
// replace with interner key in presence of (string/identifier) interner.
pub type SymId = u32;

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Name {
    /// To be used for interned lowercase identifiers
    Lower(SymId),
    /// To be used for interned uppercase identifiers
    Upper(SymId),
    /// Uniquely generated variables
    Fresh(Ty),
    /// Catch-all to be used for displaying names
    Named(&'static str),
}

impl Name {
    pub fn display<'store>(&self, lexicon: &'store Lexicon) -> Cow<'store, str> {
        match self {
            Name::Lower(s) | Name::Upper(s) => (&lexicon[Sym::new(*s)]).into(),
            Name::Fresh(ty) => ty.display().into(),
            Name::Named(s) => Cow::from(*s),
        }
    }

    /// For variants holding keys for interned strings. Since by
    /// convention, the `Sym` type would be used as keys to lookup
    /// interned names, this would allow extraction of the key held
    /// for further identifier/name lookup.
    pub fn get_sym(&self) -> Option<Sym> {
        match self {
            Name::Lower(s) | Name::Upper(s) => Some(Sym::new(*s)),
            _ => None,
        }
    }
}

pub trait Fresh {
    /// Representative
    type Repr: Hashy;
    fn fresh(&mut self) -> Self::Repr;
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Ty(pub SymId);

impl Ty {
    pub fn fresh(state: SymId) -> Self {
        Ty(state + 1)
    }

    pub fn display(&self) -> String {
        let mut name = String::new();
        let mut tmp = self.0 as usize;
        let azs = ('a'..='z').collect::<Vec<char>>();
        let mut ct = 0;
        loop {
            if tmp < 26 {
                name.push(azs[tmp]);
                break;
            } else {
                name.push(azs[ct % 26]);
                ct += 1;
                tmp -= 26;
            }
        }
        name
    }
}

impl std::fmt::Display for Ty {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.display())
    }
}

impl std::fmt::Display for Name {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Name::Named(s) = self {
            write!(f, "{}", s)
        } else {
            // will only display u32 for `Upper` and `Lower` variants -- use
            // `display` method wih interner if possible.
            write!(f, "{:?}", self)
        }
    }
}

pub fn display_fresh(s: SymId) -> String {
    let index = s as usize;
    let mut name = String::new();
    let mut tmp = index;
    let azs = ('a'..='z').collect::<Vec<char>>();
    let mut ct = 0;
    loop {
        if tmp < 26 {
            name.push(azs[tmp]);
            break;
        } else {
            name.push(azs[ct % 26]);
            ct += 1;
            tmp -= 26;
        }
    }
    name
}
