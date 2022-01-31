use std::collections::{HashMap, HashSet};

use crate::{name::Var, types::Type, Hashy};

pub trait Substitutable {
    type Id: Hashy;
    fn ftv(&self) -> HashSet<Self::Id>;

    fn apply(&self, sub: &Subst) -> Self;

    fn apply_mut(&mut self, subst: &Subst) -> &mut Self
    where
        Self: Sized,
    {
        *self = self.apply(subst);
        self
    }

    fn occurs_check(&self, id: &Self::Id) -> bool {
        self.ftv().contains(id)
    }
}

impl<T> Substitutable for Vec<T>
where
    T: Substitutable,
{
    type Id = T::Id;
    fn ftv(&self) -> HashSet<Self::Id> {
        let mut base = HashSet::new();
        for t in self {
            base.extend(t.ftv());
        }
        base
    }
    fn apply(&self, subst: &Subst) -> Self {
        self.iter().map(|t| t.apply(subst)).collect()
    }
}

#[derive(Clone, Debug, PartialEq, Default)]
pub struct Subst(pub HashMap<Var, Type>);

impl Subst {
    pub fn singleton(var: Var, ty: Type) -> Subst {
        Subst(HashMap::from([(var, ty)]))
    }

    pub fn empty() -> Self {
        Self::default()
    }

    pub fn get(&self, name: &Var) -> Option<&Type> {
        self.0.get(name)
    }

    /// Returns a substitution obtained by composing this substitution
    /// with another.
    pub fn compose(&self, sub2: &Self) -> Self {
        let mut s3 = sub2
            .0
            .iter()
            .map(|(n, t)| (*n, t.apply(self)))
            .collect::<HashMap<_, _>>();
        s3.extend(self.0.clone());
        Subst(s3)
    }
}

// impl<I> From<I> for Subst
// where
//     I: Iterator<Item = (Var, Type)>,
// {
//     fn from(iter: I) -> Self {
//         Subst(iter.collect())
//     }
// }

impl<const N: usize> From<[(Var, Type); N]> for Subst {
    fn from(entries: [(Var, Type); N]) -> Self {
        Subst(entries.iter().cloned().collect::<HashMap<_, _>>())
    }
}

impl std::fmt::Display for Subst {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.0.is_empty() {
            writeln!(f, "Subst {{}}")?;
        } else {
            writeln!(f, "Subst | ")?;
            for (v, t) in &self.0 {
                writeln!(f, "      | {} : {}", v, t)?;
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod test {
    use crate::{envr::Envr, literal::Lit, name::Var, types::Type};

    use super::*;

    #[test]
    fn test_composition() {
        let ty1 = Type::Lam(Box::new(Type::Var(Var(3))), Box::new(Type::Var(Var(4))));
        let sub1 = Subst::from([
            (
                Var(0),
                Type::Lam(Box::new(Type::Lit(Lit::Str)), Box::new(Type::Lit(Lit::Str))),
            ),
            // (
            //     Var(2),
            //     Type::Lam(Box::new(Type::Var(Var(3))), Box::new(Type::Var(Var(4)))),
            // ),
        ]);

        let sub2 = Subst::from([(
            Var(2),
            Type::Lam(Box::new(Type::Var(Var(3))), Box::new(Type::Var(Var(4)))),
        )]);

        println!("sub1: {}", &sub1);
        println!("sub2: {}", &sub2);

        // let mut envr = Envr::new();

        let comp1 = sub1.compose(&sub2);
        let comp2 = sub2.compose(&sub1);

        println!("comp1: {}", &comp1);
        println!("comp2: {}", &comp2);
    }
}
