use std::{
    collections::HashSet,
    fmt::Write,
    ops::{Add, AddAssign, Neg, Sub},
};

use crate::{
    envr::Envr,
    failure::{Failure, Solve},
    infer::Infer,
    literal::{Lit, Literal},
    name::{Name, Ty},
    pretty::Many,
    subst::{Subst, Substitutable},
    Hashy,
};

#[allow(unused)]
pub struct Counter<N> {
    count: N,
}

#[allow(unused)]
impl<N> Counter<N>
where
    N: Copy + Hashy + Add<Output = N> + AddAssign + Sub<Output = N> + Neg<Output = N> + From<u32>,
{
    pub const MAX: u32 = u32::MAX;

    pub fn increment(&mut self) -> N {
        let n = self.count;
        self.count += (1u32).into();
        n
    }

    pub fn available(&self) -> N {
        -self.count + Self::MAX.into()
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Type {
    Lit(Lit),
    Var(Ty),
    Con(Name),
    Lam(Box<Type>, Box<Type>),
    List(Box<Type>),
    Tuple(Vec<Type>),
}

pub mod constants {
    #![allow(unused)]
    use crate::literal::Lit;

    use super::Type;

    pub const UNIT: Type = Type::Lit(Lit::Unit);
    pub const BOOL: Type = Type::Lit(Lit::Bool);
    pub const INT: Type = Type::Lit(Lit::Int);
    pub const CHAR: Type = Type::Lit(Lit::Char);
    pub const STR: Type = Type::Lit(Lit::Str);
    pub const DOUBLE: Type = Type::Lit(Lit::Double);
    pub const FLOAT: Type = Type::Lit(Lit::Float);
}

pub use constants::*;

impl Type {
    pub const UNIT: Type = Type::Lit(Lit::Unit);
    pub const BOOL: Type = Type::Lit(Lit::Bool);
    pub const INT: Type = Type::Lit(Lit::Int);
    pub const CHAR: Type = Type::Lit(Lit::Char);
    pub const STR: Type = Type::Lit(Lit::Str);

    pub fn boxed(self) -> Box<Type> {
        Box::new(self)
    }

    pub fn box_cloned(&self) -> Box<Type> {
        Box::new(self.clone())
    }

    pub fn instantiate(&self, engine: &mut Infer) -> Solve<Type> {
        let scheme = self.generalize(&engine.envr);
        engine.instantiate(&scheme)
    }

    pub fn generalize(&self, env: &Envr) -> Scheme {
        let tipo = self.clone();
        let poly = self
            .ftv()
            .difference(&env.ftv())
            .copied()
            .collect::<Vec<_>>();
        Scheme { poly, tipo }
    }

    pub fn normalize(&self) -> Solve<Type> {
        match self {
            Type::Lit(_) | Type::Con(_) => Ok(self.clone()),
            Type::Var(a) => {
                let ords = Self::enumerate(self);
                let lookup = ords.into_iter().find(|(u, _)| a == u);
                if let Some((_u, v)) = lookup {
                    Ok(Type::Var(v))
                } else {
                    Err(Failure::NotInSignature(Type::Var(*a)))
                }
            }
            Type::Lam(a, b) => Ok(Type::Lam(a.normalize()?.boxed(), b.normalize()?.boxed())),
            Type::List(a) => Ok(Type::List(a.normalize()?.boxed())),
            Type::Tuple(ts) => {
                let normed = ts.iter().fold(Ok(vec![]), |a, c| {
                    let mut acc = a?;
                    let t = c.normalize()?;
                    acc.push(t);
                    Ok(acc)
                });
                Ok(Type::Tuple(normed?))
            }
        }
    }

    pub fn enumerate(&self) -> Vec<(Ty, Ty)> {
        let mut vars = Self::fv(self);
        vars.dedup();
        vars.iter()
            .zip(0u32..)
            .map(|(v, i)| (*v, Ty(i)))
            .collect::<Vec<_>>()
    }

    pub fn fv(&self) -> Vec<Ty> {
        match self {
            Type::Var(a) => vec![*a],
            Type::Lit(_) | Type::Con(_) => vec![],
            Type::Lam(x, y) => {
                let mut a = x.fv();
                a.extend(y.fv());
                a
            }
            Type::List(a) => a.fv(),
            Type::Tuple(ts) => ts.iter().flat_map(|t| t.fv()).collect(),
        }
    }
}

impl From<Lit> for Type {
    fn from(lit: Lit) -> Self {
        match lit {
            Lit::Unit => UNIT,
            Lit::Bool => BOOL,
            Lit::Int => INT,
            Lit::Char => CHAR,
            Lit::Str => STR,
            Lit::Float => FLOAT,
            Lit::Double => DOUBLE,
        }
    }
}

impl From<Literal> for Type {
    fn from(lit: Literal) -> Self {
        match lit {
            Literal::Unit => UNIT,
            Literal::Bool(_) => BOOL,
            Literal::Int(_) => INT,
            Literal::Char(_) => CHAR,
            Literal::Str(_) => STR,
            Literal::Float(_) => FLOAT,
            Literal::Double(_) => DOUBLE,
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
            Type::List(a) => write!(f, "[{}]", a),
            Type::Tuple(ts) => {
                let len = ts.len() - 1;
                f.write_char('(')?;
                for (i, t) in ts.iter().enumerate() {
                    write!(f, "{}", t)?;
                    if i < len {
                        f.write_str(", ")?;
                    }
                }
                f.write_char(')')
            }
        }
    }
}

impl Substitutable for Type {
    fn ftv(&self) -> HashSet<Ty> {
        match self {
            Type::Lit(_) | Type::Con(_) => [].into(),
            Type::Var(n) => [*n].into(),
            Type::Lam(a, b) => {
                let t1 = a.ftv();
                let t2 = b.ftv();
                // tvs =
                t1.union(&t2).cloned().collect()
            }
            Type::List(a) => a.ftv(),
            Type::Tuple(ts) => ts.ftv(),
        }
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
                Type::Lam(t1.boxed(), t2.boxed())
            }
            Type::List(a) => {
                let t = a.apply(sub);
                Type::List(t.boxed())
            }
            Type::Tuple(ts) => Type::Tuple(ts.apply(sub)),
        }
    }
}

// example: id :: forall a. a -> a
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Scheme {
    /// Polymorphic type variables
    pub poly: Vec<Ty>,
    pub tipo: Type,
}

impl Scheme {
    pub fn monotype(tipo: Type) -> Scheme {
        Scheme { poly: vec![], tipo }
    }

    pub fn normalize(&self) -> Solve<Scheme> {
        let poly = self
            .tipo
            .clone()
            .enumerate()
            .into_iter()
            .map(|(_, snd)| snd)
            .collect::<Vec<_>>();
        let tipo = self.tipo.normalize()?;
        Ok(Scheme { poly, tipo })
    }
}

impl Substitutable for Scheme {
    fn ftv(&self) -> HashSet<Ty> {
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
        if self.poly.is_empty() {
            write!(f, "{}", &self.tipo)
        } else {
            write!(f, "forall ")?;
            write!(f, "{}", Many(&self.poly[..], ' '))?;
            write!(f, ". {}", self.tipo)
        }
    }
}

#[cfg(test)]
mod test {
    #![allow(unused)]
    use super::*;

    fn func(t1: Type, t2: Type) -> Type {
        Type::Lam(Box::new(t1), Box::new(t2))
    }

    #[test]
    fn test_scheme() {}
}
