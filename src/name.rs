/// For greater efficiency, identifiers (outside of the scope of this toy
/// crate) should be interned, as it would mean passing around "interner
/// keys", which should be more lightweight assuming the interner key
/// (denoted `Sym` here) has a smaller size than a `String` or a string
/// slice. The `Sym` type, while a simple type alias here, should
/// ultimately be a `newtype` for string interner keys.
///
/// For a simple string interner, we may assume that static string slices
/// are stored and retrieved via a key -- in this case, since this toy
/// crate doesn't include an actual string interner, the mere skeleton is
/// included for completeness' sake.
// replace with interner key in presence of (string/identifier) interner.
pub type Sym = u32;

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Name {
    /// To be used for interned lowercase identifiers
    Lower(Sym),
    /// To be used for interned uppercase identifiers
    Upper(Sym),
    /// Uniquely generated variables
    Fresh(Var),
    /// Catch-all to be used for displaying names
    Named(&'static str),
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Var(pub Sym);

impl Var {
    pub fn fresh(state: Sym) -> Self {
        Var(state + 1)
    }

    pub fn display(&self) -> String {
        let index = self.0 as usize;
        let mut name = String::new();
        let mut tmp = index.clone();
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

impl std::fmt::Display for Var {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.display())
    }
}

impl Name {
    /// For variants holding keys for interned strings. Since by
    /// convention, the `Sym` type would be used as keys to lookup
    /// interned names, this would allow extraction of the key held
    /// for further identifier/name lookup.
    pub fn get_sym(&self) -> Option<Sym> {
        match self {
            Name::Lower(n) | Name::Upper(n) | Name::Fresh(Var(n)) => Some(*n),
            Name::Named(_) => None,
        }
    }
}

impl std::fmt::Display for Name {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Name::Named(s) = self {
            write!(f, "{}", s)
        } else {
            write!(f, "{:?}", self)
        }
    }
}

pub fn display_fresh(s: Sym) -> String {
    let index = s as usize;
    let mut name = String::new();
    let mut tmp = index.clone();
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
