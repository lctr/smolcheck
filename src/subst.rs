use std::collections::{HashMap, HashSet};

use crate::{name::Ty, types::Type};

pub trait Substitutable {
    fn ftv(&self) -> HashSet<Ty>;

    fn apply(&self, sub: &Subst) -> Self;

    fn apply_mut(&mut self, subst: &Subst) -> &mut Self
    where
        Self: Sized,
    {
        *self = self.apply(subst);
        self
    }
}

pub fn occurs_check(s: &impl Substitutable, var: Ty) -> bool {
    s.ftv().contains(&var)
}

impl<T> Substitutable for Vec<T>
where
    T: Substitutable,
{
    fn ftv(&self) -> HashSet<Ty> {
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
pub struct Subst(pub HashMap<Ty, Type>);

impl Subst {
    pub fn singleton(var: Ty, ty: Type) -> Subst {
        Subst(HashMap::from([(var, ty)]))
    }

    pub fn empty() -> Self {
        Self::default()
    }

    pub fn get(&self, name: &Ty) -> Option<&Type> {
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

impl<const N: usize> From<[(Ty, Type); N]> for Subst {
    fn from(entries: [(Ty, Type); N]) -> Self {
        Subst(entries.iter().cloned().collect::<HashMap<_, _>>())
    }
}

impl std::fmt::Display for Subst {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{{")?;
        let mut br = "";
        match self.0.len() {
            0 => {}
            n => {
                let mut w = self.0.iter().collect::<Vec<_>>();
                w.sort_by_key(|(v, _)| *v);
                let i = if n == 1 {
                    let (v, t) = w[0];
                    write!(f, " [{} := {}] ", v, t)?;
                    1
                } else {
                    br = "\n";
                    0
                };
                for (v, t) in &w[i..] {
                    write!(f, "{} [{} := {}] ", br, v, t)?;
                }
            }
        }
        write!(f, "{}}}", br)
    }
}

#[cfg(test)]
mod test {
    use crate::{
        envr::Envr,
        literal::Lit,
        name::Ty,
        types::{Type, STR},
    };

    use super::*;

    #[test]
    fn inspect_composition() {
        fn var(n: u32) -> Type {
            Type::Var(Ty(n))
        }

        let ty1 = Type::Lam(Type::Var(Ty(3)).boxed(), STR.boxed());

        let sub1 = Subst::from([(Ty(0), Type::Lam(STR.boxed(), var(4).boxed()))]);

        let sub2 = Subst::from([(
            Ty(2),
            Type::Lam(Box::new(Type::Var(Ty(3))), Box::new(Type::Var(Ty(4)))),
        )]);

        println!("sub1: {}", &sub1);
        println!("sub2: {}", &sub2);

        // let mut envr = Envr::new();

        let comp1 = sub1.compose(&sub2);
        let comp2 = sub2.compose(&sub1);

        println!("comp1: {}", &comp1);
        println!("comp2: {}", &comp2);

        let tvcomp12 = ty1.apply(&comp1.compose(&comp2));
        println!("comp1 |> comp2: {}", tvcomp12);
    }
}
