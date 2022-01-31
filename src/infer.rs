use std::collections::{HashMap, HashSet};

use crate::{
    envr::Envr,
    expr::{Decl, Declaration, Expr, Expression},
    name::{Name, Sym, Var},
    subst::{Subst, Substitutable},
    types::{Scheme, Type},
};

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Failure {
    NotUnified(Type, Type),
    Infinite(Type, Type),
    NotFunc(Type),
    Unbound(Name),
    Ambiguous(Vec<Constraint>),
    Mismatch(Vec<Type>, Vec<Type>),
    NotInSignature(Type),
}

impl std::error::Error for Failure {}

impl std::fmt::Display for Failure {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Unification failure: ")?;
        match self {
            Failure::NotUnified(t1, t2) => write!(
                f,
                "not unified! Unable to unify the type\n\t`{}`\nwith the type\n\t`{}`",
                t1, t2
            ),
            Failure::Infinite(v, t) => write!(
                f,
                "occurs check! Cannot unify the infinite type `{}` ~ `{}`",
                v, t
            ),
            Failure::NotFunc(t) => {
                write!(f, "not callable! The type\n\t`{}`\n\tis not a function!", t)
            }
            Failure::Unbound(n) => write!(
                f,
                "unbound variable! The identifier `{}` is not in scope.",
                n
            ),
            Failure::Ambiguous(cs) => {
                writeln!(
                    f,
                    "ambiguous constraints! The following constraints were found to be ambiguous:"
                )?;
                for (x, y) in cs {
                    writeln!(f, "\t{} => {}", x, y)?;
                }
                Ok(())
            }
            Failure::Mismatch(x, y) => {
                write!(
                    f,
                    "type mismatch! Failed to unify due to type mismatch(es)\n\t{:?}\n\t{:?}",
                    x, y
                )
            }
            Failure::NotInSignature(t) => {
                write!(
                    f,
                    "not in signature. Type variable `{}` is not in signature!",
                    t
                )
            }
        }
    }
}

#[derive(Clone, Debug, Default)]
pub struct Infer {
    pub count: Sym,
    pub envr: Envr,
}

impl Infer {
    pub fn new() -> Infer {
        Infer::default()
    }

    pub fn fresh(&mut self) -> Type {
        self.count += 1;
        Type::Var(Var(self.count.clone()))
    }

    pub fn instantiate(&mut self, scheme: &Scheme) -> Solve<Type> {
        let Scheme { poly, tipo } = scheme;
        let tvs = poly.iter().map(|_| self.fresh());
        let sub = poly
            .iter()
            .zip(tvs)
            .map(|(v, t)| (*v, t))
            .collect::<HashMap<_, _>>();
        Ok(tipo.apply(&Subst(sub)))
    }

    pub fn generalize(envr: &Envr, ty: Type) -> Scheme {
        let t_ftv = ty.clone().ftv();
        let e_ftv = envr.ftv();
        let poly = t_ftv.difference(&e_ftv).copied().collect();
        Scheme { poly, tipo: ty }
    }

    pub fn lookup_env(&mut self, k: &Name) -> Solve<Type> {
        if self.envr.contains_key(k) {
            let s = self.envr.get(k).unwrap().clone();
            self.instantiate(&s)
        } else {
            Err(Failure::Unbound(*k))
        }
    }

    /// Canonicalize and return the top-level polymorphic type
    pub fn canonicalize(ty: Type) -> Solve<Scheme> {
        let envr = Envr::default();
        Self::generalize(&envr, ty).normalize()
    }

    pub fn infer_top(&mut self, decls: &[Decl]) -> Solve<&mut Self> {
        match decls.split_first() {
            Some((Declaration(name, expr), rest)) => {
                let sch = self.infer_expr(expr)?;
                self.envr.insert(*name, sch);
                self.infer_top(rest)
            }
            None => Ok(self),
        }
    }

    pub fn infer_expr(&mut self, expr: &Expr) -> Solve<Scheme> {
        let (ty, cs) = self.infer(expr)?;
        let sub = Unifier::solve(Subst::empty(), cs.as_slice())?;
        Self::canonicalize(ty.apply(&sub))
    }

    pub fn constraints_expr(
        &mut self,
        expr: &Expr,
    ) -> Solve<(Vec<Constraint>, Subst, Type, Scheme)> {
        let (ty, cs) = self.infer(expr)?;
        let sub = Unifier::solve(Subst::empty(), cs.as_slice())?;
        let sch = Infer::canonicalize(ty.apply(&sub))?;
        Ok((cs, sub, ty, sch))
    }

    pub fn infer(&mut self, expr: &Expr) -> Solve<(Type, Vec<Constraint>)> {
        match expr {
            Expression::Lit(l) => Ok((Type::from(*l), vec![])),
            Expression::Ident(x) => {
                let t = self.lookup_env(x)?;
                Ok((t, vec![]))
            }
            Expression::Bin(op, left, right) => {
                let (t1, c1) = self.infer(left.as_ref())?;
                let (t2, c2) = self.infer(right.as_ref())?;
                let tv = self.fresh();
                let u1 = Type::Lam(
                    Box::new(t1),
                    Box::new(Type::Lam(Box::new(t2), Box::new(tv.clone()))),
                );
                let u2 = op.ret_ty();
                let cs = vec![c1, c2, vec![(u1, u2)]]
                    .into_iter()
                    .flatten()
                    .collect::<Vec<_>>();
                Ok((tv, cs))
            }
            Expression::Lam(x, e) => {
                let tv = self.fresh();
                // let mut new_env = self.envr.clone();
                // new_env.remove(k);
                self.envr.remove(x);
                let scheme = Scheme {
                    poly: vec![],
                    tipo: tv.clone(),
                };
                self.envr.insert(*x, scheme);
                let (t, c) = self.infer(e.as_ref())?;
                Ok((Type::Lam(Box::new(tv), Box::new(t)), c))
            }
            Expression::App(x, y) => {
                let (t1, c1) = self.infer(x.as_ref())?;
                let (t2, c2) = self.infer(y.as_ref())?;
                let tv = self.fresh();
                // let mut cs = vec![];
                // cs.extend(c1);
                // cs.extend(c2);
                // cs.extend(vec![(t1, Type::Lam(Box::new(t2), Box::new(tv.clone())))]);
                let constraints = vec![
                    c1,
                    c2,
                    vec![(t1, Type::Lam(Box::new(t2), Box::new(tv.clone())))],
                ]
                .into_iter()
                .flatten()
                .collect::<Vec<_>>();
                Ok((tv, constraints))
            }
            Expression::Cond(cond, then, other) => {
                let (t1, c1) = self.infer(cond.as_ref())?;
                let (t2, c2) = self.infer(then.as_ref())?;
                let (t3, c3) = self.infer(other.as_ref())?;
                let cs = vec![c1, c2, c3, vec![(t1, Type::BOOL), (t2.clone(), t3)]]
                    .into_iter()
                    .flatten()
                    .collect::<Vec<_>>();
                Ok((t2, cs))
            }
        }
    }
}

pub type Constraint = (Type, Type);

impl Substitutable for Constraint {
    type Id = Var;

    fn ftv(&self) -> HashSet<Self::Id> {
        let fvs1 = self.0.ftv();
        let fvs2 = &self.1.ftv();
        fvs1.union(fvs2).cloned().collect()
    }

    fn apply(&self, sub: &Subst) -> Self {
        let (t1, t2) = self;
        (t1.apply(sub), t2.apply(sub))
    }
}

pub type Solve<T> = Result<T, Failure>;

#[derive(Clone, Debug, PartialEq, Default)]
pub struct Unifier {
    pub sub: Subst,
    pub constraints: Vec<Constraint>,
}

impl Unifier {
    pub fn new(sub: Subst, constraints: Vec<Constraint>) -> Self {
        Unifier { sub, constraints }
    }

    pub fn from_constraints(constraints: Vec<Constraint>) -> Self {
        Unifier {
            sub: Subst::empty(),
            constraints,
        }
    }

    pub fn solve(sub: Subst, constraints: &[Constraint]) -> Solve<Subst> {
        let cs = constraints;
        match cs.split_first() {
            Some((head, rest)) => {
                let (t1, t2) = head.clone();
                let s1 = Self::unifies(t1, t2)?;
                let s2 = s1.compose(&sub);
                let tail = rest.to_vec().apply(&s1);
                Self::solve(sub, tail.as_slice())
            }
            None => Ok(sub),
        }
    }

    pub fn unifies(t1: Type, t2: Type) -> Solve<Subst> {
        if t1 == t2 {
            Ok(Subst::empty())
        } else {
            match (t1, t2) {
                (Type::Var(v), t) => Self::bind(v, t),
                (t, Type::Var(v)) => Self::bind(v, t),
                (Type::Lam(x1, y1), Type::Lam(x2, y2)) => {
                    Self::unify_many(&[*x1, *y1], &[*x2, *y2])
                }
                (x, y) => Err(Failure::Infinite(x, y)),
            }
        }
    }

    pub fn unify_many(t1s: &[Type], t2s: &[Type]) -> Solve<Subst> {
        match (t1s.split_first(), t2s.split_first()) {
            (None, None) => Ok(Subst::empty()),
            (Some((x0, xs)), Some((y0, ys))) => {
                let s1 = Self::unifies(x0.clone(), y0.clone())?;
                let sx = xs.to_vec().apply(&s1);
                let sx = sx.as_slice();
                let sy = ys.to_vec().apply(&s1);
                let sy = sy.as_slice();
                let s2 = Self::unify_many(sx, sy)?;
                Ok(s2.compose(&s1))
            }
            _ => Err(Failure::Mismatch(t1s.to_vec(), t2s.to_vec())),
        }
    }

    pub fn bind(var: Var, ty: Type) -> Solve<Subst> {
        match ty {
            Type::Var(v) if v == var => Ok(Subst::empty()),
            t if t.occurs_check(&var) => Err(Failure::Infinite(Type::Var(var), t)),
            _ => Ok([(var, ty)].into()),
        }
    }
}

#[cfg(test)]
mod test {
    use crate::{expr::PrimOp, literal::Literal};

    use super::*;

    #[test]
    pub fn test_infer_lambda() {
        let lam = Expr::Lam(
            Name::Named("x"),
            Box::new(Expr::Bin(
                PrimOp::Add,
                Box::new(Expr::Ident(Name::Named("x"))),
                Box::new(Expr::Lit(Literal::Int(5))),
            )),
        );

        let mut checker = Infer::new();

        println!("source: `\\x -> x + 5`\nlambda: {:#?}", &lam);
        match checker.infer(&lam) {
            Ok(res) => println!(
                "inference results (type, constraints):\n\t({}, {:#?})",
                &res.0, &res.1
            ),
            Err(e) => println!("{}", e),
        }
    }

    #[test]
    pub fn fails_unbound_var() {
        let cond = Expr::Cond(
            Box::new(Expr::Bin(
                PrimOp::Eq,
                Box::new(Expr::Ident(Name::Named("x"))),
                Box::new(Expr::Lit(Literal::Int(5))),
            )),
            Box::new(Expression::Lit(Literal::Int(10))),
            Box::new(Expression::Bin(
                PrimOp::Mul,
                Box::new(Expr::Ident(Name::Named("x"))),
                Box::new(Expr::Lit(Literal::Int(10))),
            )),
        );

        let mut checker = Infer::new();

        println!(
            "source: `if x == 5 then 10 else x + 10`\nlambda: {:#?}",
            &cond
        );
        match checker.infer(&cond) {
            Ok(res) => println!(
                "inference results (type, constraints):\n\t({}, {:#?})\n\nenvironment: {:#?}",
                &res.0, &res.1, &checker.envr
            ),
            Err(e) => println!("{}", e),
        };
    }
}
