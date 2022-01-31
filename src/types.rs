use std::collections::{HashMap, HashSet};

use crate::{
    envr::Envr,
    infer::{Failure, Solve},
    literal::{Lit, Literal},
    name::{display_fresh, Name, Sym, Var},
    subst::{Subst, Substitutable},
};

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Type {
    Lit(Lit),
    Var(Var),
    Con(Name),
    Lam(Box<Type>, Box<Type>),
}

impl Type {
    pub const BOOL: Type = Type::Lit(Lit::Bool);
    pub const INT: Type = Type::Lit(Lit::Int);
    pub const CHAR: Type = Type::Lit(Lit::Char);
    pub const STR: Type = Type::Lit(Lit::Str);

    pub fn fresh(old_count: Sym) -> Type {
        Type::Var(Var::fresh(old_count))
    }

    pub fn boxed(self) -> Box<Type> {
        Box::new(self)
    }

    pub fn generalize(self, env: &Envr) -> Scheme {
        let tipo = self.clone();
        let poly = self
            .ftv()
            .difference(&env.ftv())
            .map(|tv| *tv)
            .collect::<Vec<_>>();
        Scheme { poly, tipo }
    }
}

impl From<Lit> for Type {
    fn from(lit: Lit) -> Self {
        match lit {
            Lit::Bool => Type::BOOL,
            Lit::Int => Type::INT,
            Lit::Char => Type::CHAR,
            Lit::Str => Type::STR,
        }
    }
}

impl From<Literal> for Type {
    fn from(lit: Literal) -> Self {
        match lit {
            Literal::Bool(b) => Type::BOOL,
            Literal::Int(i) => Type::INT,
            Literal::Char(c) => Type::CHAR,
            Literal::Str(s) => Type::STR,
        }
    }
}

impl std::fmt::Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Type::Lit(lit) => write!(f, "{}", lit),
            Type::Var(n) => write!(f, "{}", n),
            Type::Con(n) => write!(f, "{}", n),
            Type::Lam(a, b) => {
                write!(f, "{} -> {}", a, b)
            }
        }
    }
}

impl Substitutable for Type {
    type Id = Var;

    fn ftv(&self) -> HashSet<Self::Id> {
        let mut tvs = HashSet::new();
        match self {
            // Type::Prim(_) |
            Type::Lit(_) | Type::Con(_) => {}
            Type::Var(n) => {
                tvs.insert(*n);
            }
            Type::Lam(a, b) => {
                let t1 = a.ftv();
                let t2 = b.ftv();
                tvs = t1.union(&t2).cloned().collect();
            }
        };
        tvs
    }

    fn apply(&self, sub: &Subst) -> Self {
        match self {
            Type::Lit(_) | Type::Con(_) => self.clone(),
            Type::Var(ref n) => match sub.get(n) {
                Some(ty) => ty.clone(),
                None => self.clone(),
            },
            Type::Lam(x, y) => {
                let t1 = x.apply(sub);
                let t2 = y.apply(sub);
                Type::Lam(Box::new(t1), Box::new(t2))
            }
        }
    }
}

// example: id :: forall a. a -> a
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Scheme {
    /// Polymorphic type variables
    pub poly: Vec<Var>,
    pub tipo: Type,
}

impl Scheme {
    pub fn normalize(&self) -> Solve<Scheme> {
        let poly = Self::order(&self.tipo.clone())
            .into_iter()
            .map(|(_, snd)| snd)
            .collect::<Vec<_>>();
        let tipo = Self::norm_ty(&self.tipo)?;
        Ok(Scheme { poly, tipo })
    }

    fn norm_ty(body: &Type) -> Solve<Type> {
        match body {
            Type::Var(a) => {
                let ords = Self::order(body);
                let lookup = ords.into_iter().find(|(u, v)| a == u);
                if let Some((u, v)) = lookup {
                    Ok(Type::Var(v))
                } else {
                    Err(Failure::NotInSignature(Type::Var(*a)))
                }
            }
            Type::Lit(_) | Type::Con(_) => Ok(body.clone()),
            Type::Lam(a, b) => Ok(Type::Lam(
                Self::norm_ty(a.as_ref())?.boxed(),
                Self::norm_ty(b.as_ref())?.boxed(),
            )),
        }
    }

    fn order(body: &Type) -> Vec<(Var, Var)> {
        let mut vars = Self::fv(body);
        vars.dedup();
        vars.iter()
            .zip(0u32..)
            .map(|(v, i)| (*v, Var(i)))
            .collect::<Vec<_>>()
    }

    fn fv(body: &Type) -> Vec<Var> {
        match body {
            Type::Var(a) => vec![*a],
            Type::Lit(_) | Type::Con(_) => vec![],
            Type::Lam(x, y) => {
                let mut a = Scheme::fv(x.as_ref());
                a.extend(Scheme::fv(y.as_ref()));
                a
            }
        }
    }
}

impl Substitutable for Scheme {
    type Id = Var;

    fn ftv(&self) -> HashSet<Self::Id> {
        let vs = self.poly.iter().cloned().collect();
        self.tipo.ftv().difference(&vs).cloned().collect()
    }

    fn apply(&self, sub: &Subst) -> Self {
        let poly = self.poly.clone();

        let s = Subst(poly.iter().fold(sub.0.clone(), |mut a, c| {
            a.remove(c);
            a
        }));

        Self {
            poly,
            tipo: self.tipo.apply(&s),
        }
    }
}

impl std::fmt::Display for Scheme {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "forall ")?;
        for v in self.poly.iter() {
            write!(f, "{} ", v.display())?;
        }
        write!(f, ". {}", self.tipo)
    }
}

#[cfg(test)]
mod test {
    use super::*;

    fn func(t1: Type, t2: Type) -> Type {
        Type::Lam(Box::new(t1), Box::new(t2))
    }

    #[test]
    fn test_scheme() {}
}
