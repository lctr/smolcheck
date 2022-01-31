pub type Sym = u32;

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Name {
    Ident(Sym),
    Const(Sym),
    /// Uniquely generated variables
    Fresh(Var),
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
    pub fn get_sym(&self) -> Option<Sym> {
        match self {
            Name::Ident(n) | Name::Const(n) | Name::Fresh(Var(n)) => Some(*n),
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
