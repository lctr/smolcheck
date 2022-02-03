use crate::{
    constraint::Constraint,
    failure::{Failure, Solve},
    name::Ty,
    subst::{occurs_check, Subst, Substitutable},
    types::Type,
};

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
        Unifier::new(sub, constraints.to_vec()).solver()
    }

    pub fn solver(self) -> Solve<Subst> {
        let Unifier {
            mut sub,
            mut constraints,
        } = self;

        if constraints.is_empty() {
            return Ok(sub);
        }

        constraints.reverse();

        let mut tmp;
        loop {
            if constraints.is_empty() {
                break;
            }

            tmp = constraints.split_off(1);

            if tmp.is_empty() {
                break;
            }

            let Constraint(t1, t2) = tmp.pop().unwrap();

            let s1 = Self::unifies(t1, t2)?;
            let s2 = s1.compose(&sub);
            constraints = constraints.apply(&s1);

            sub = s2;
        }

        Ok(sub)
    }

    pub fn unifies(t1: Type, t2: Type) -> Solve<Subst> {
        if t1 == t2 {
            Ok(Subst::empty())
        } else {
            match (t1, t2) {
                (Type::Lit(x), Type::Lit(y)) => {
                    if x == y {
                        Ok(Subst::empty())
                    } else {
                        Err(Failure::NotUnified(Type::Lit(x), Type::Lit(y)))
                    }
                }
                // (Type::List(x), Type::Var(t)) | (Type::Var(t), Type::List(x)) => {
                //     if occurs_check(x.as_ref(), t) {
                //         Err(Failure::Infinite(Type::Var(t), *x))
                //     } else {
                //         Self::bind(t, *x)
                //     }
                // }
                (Type::List(x), Type::List(y)) => Self::unifies(*x, *y),
                (Type::Con(x), Type::Con(y)) if x == y => Ok(Subst::empty()),
                (Type::Var(v), t) => Self::bind(v, t),
                (t, Type::Var(v)) => Self::bind(v, t),
                (Type::Lam(x1, y1), Type::Lam(x2, y2)) => {
                    Self::unify_many(&[*x1, *y1], &[*x2, *y2])
                }
                (Type::Tuple(xs), Type::Tuple(ys)) => Self::zip_unify(xs, ys),
                (x, y) => Err(Failure::Infinite(x, y)),
            }
        }
    }

    // measure/compare this with `unify_many`
    pub fn zip_unify(xs: Vec<Type>, ys: Vec<Type>) -> Solve<Subst> {
        xs.into_iter()
            .zip(ys)
            .fold(Ok(Subst::empty()), |a, (tx, ty)| {
                let acc = a?;
                // a.and_then(|a| Ok(compose(a, unify(tx, ty)?)))
                let comp = Self::unifies(tx, ty)?;
                Ok(acc.compose(&comp))
            })
    }

    // measure/compare this with `zip_unify`
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

    pub fn bind(var: Ty, ty: Type) -> Solve<Subst> {
        match ty {
            Type::Var(v) if v == var => Ok(Subst::empty()),
            t if occurs_check(&t, var) => Err(Failure::Infinite(t, Type::Var(var))),
            _ => Ok(Subst::singleton(var, ty)),
        }
    }
}
