use std::collections::HashSet;

use crate::{
    name::Var,
    subst::{Subst, Substitutable},
    types::Type,
};

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Constraint(pub Type, pub Type);

impl Constraint {
    pub fn ppr_slice(cs: &[Constraint]) {
        for c in cs {
            println!("\t{}", c);
        }
    }
}

impl From<(Type, Type)> for Constraint {
    fn from((t1, t2): (Type, Type)) -> Self {
        Constraint(t1, t2)
    }
}

impl std::fmt::Display for Constraint {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "({}, {})", &self.0, &self.1)
    }
}

impl Substitutable for Constraint {
    fn ftv(&self) -> HashSet<Var> {
        let fvs1 = self.0.ftv();
        let fvs2 = &self.1.ftv();
        fvs1.union(fvs2).cloned().collect()
    }

    fn apply(&self, sub: &Subst) -> Self {
        let Constraint(t1, t2) = self;
        Constraint(t1.apply(sub), t2.apply(sub))
    }
}
