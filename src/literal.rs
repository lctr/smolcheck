#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum Lit {
    Unit,
    Bool,
    Int,
    Char,
    Str,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum Literal {
    Unit,
    Bool(bool),
    Int(i32),
    Char(char),
    Str(&'static str),
}

impl std::fmt::Display for Lit {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if matches!(self, Self::Unit) {
            write!(f, "()")
        } else {
            write!(f, "{:?}", &self)
        }
    }
}
