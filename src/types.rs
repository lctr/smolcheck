use std::{collections::HashSet, fmt::Write};

use crate::{
    envr::Envr,
    failure::{Failure, Solve},
    literal::{Lit, Literal},
    name::{Name, Var},
    subst::{Subst, Substitutable},
};

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Type {
    Lit(Lit),
    Var(Var),
    Con(Name),
    Lam(Box<Type>, Box<Type>),
    List(Box<Type>),
    Tuple(Vec<Type>),
}

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

    pub fn generalize(self, env: &Envr) -> Scheme {
        let tipo = self.clone();
        let poly = self
            .ftv()
            .difference(&env.ftv())
            .map(|tv| *tv)
            .collect::<Vec<_>>();
        Scheme { poly, tipo }
    }

    fn normalize(&self) -> Solve<Type> {
        match self {
            Type::Lit(_) | Type::Con(_) => Ok(self.clone()),
            Type::Var(a) => {
                let ords = Self::order(self);
                let lookup = ords.into_iter().find(|(u, v)| a == u);
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

    fn order(&self) -> Vec<(Var, Var)> {
        let mut vars = Self::fv(self);
        vars.dedup();
        vars.iter()
            .zip(0u32..)
            .map(|(v, i)| (*v, Var(i)))
            .collect::<Vec<_>>()
    }

    fn fv(&self) -> Vec<Var> {
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
            Lit::Unit => Type::UNIT,
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
            Literal::Unit => Type::UNIT,
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
    fn ftv(&self) -> HashSet<Var> {
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
    pub poly: Vec<Var>,
    pub tipo: Type,
}

impl Scheme {
    pub fn normalize(&self) -> Solve<Scheme> {
        let poly = self
            .tipo
            .clone()
            .order()
            .into_iter()
            .map(|(_, snd)| snd)
            .collect::<Vec<_>>();
        let tipo = self.tipo.normalize()?;
        Ok(Scheme { poly, tipo })
    }
}

impl Substitutable for Scheme {
    fn ftv(&self) -> HashSet<Var> {
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

#[derive(Clone, Debug)]
pub struct Many<'a, A>(pub &'a [A]);

impl<'a, A> std::fmt::Display for Many<'a, A>
where
    A: std::fmt::Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_char('\n')?;
        for a in self.0 {
            write!(f, "\t")?;
            A::fmt(a, f)?;
        }
        Ok(())
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
