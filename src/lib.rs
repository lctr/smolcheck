pub mod constraint;
pub mod envr;
pub mod expr;
pub mod failure;
pub mod infer;
pub mod literal;
pub mod name;
pub mod pretty;
pub mod subst;
pub mod types;
pub mod unify;

pub trait Hashy: Clone + Eq + std::hash::Hash {}

impl<T> Hashy for T where T: Clone + Eq + std::hash::Hash {}

pub use name::display_fresh;

pub use constraint::Constraint;
pub use failure::{Failure, Solve};
pub use literal::*;
pub use name::Fresh;
pub use name::Name as Identifier;
use subst::Substitutable;
pub use unify::Unifier;

pub type Constraints = Vec<Constraint>;

#[derive(Clone, Debug)]
pub struct Inferred {
    pub expr: expr::Expr,
    pub constraints: Constraints,
    pub subst: subst::Subst,
    pub tipo: types::Type,
    pub scheme: types::Scheme,
    pub engine: infer::Infer,
}

impl Inferred {
    pub fn get_count(&self) -> u32 {
        self.engine.count
    }
    pub fn get_subst(&self) -> &subst::Subst {
        &self.subst
    }
    pub fn get_constraints(&self) -> &[Constraint] {
        &self.constraints[..]
    }
    pub fn apply_sub(&self) -> types::Type {
        self.tipo.apply(self.get_subst())
    }
    pub fn resolve(self) -> Solve<Inferred> {
        let constraints = self.constraints;
        let subst = Unifier::solve(self.subst, &constraints[..])?;
        let tipo = self.tipo.apply(&subst);
        let scheme = self.scheme.apply(&subst);
        let expr = self.expr;
        let engine = self.engine;
        Ok(Inferred {
            subst,
            tipo,
            scheme,
            constraints,
            expr,
            engine,
        })
    }
}

pub fn run_inference<X: Into<expr::Expr>>(ex: X) -> Solve<Inferred> {
    let expr: expr::Expr = ex.into();
    let mut engine = infer::Infer::new();
    let (constraints, subst, tipo, scheme) = engine.constraints_expr(&expr)?;
    Ok(Inferred {
        expr,
        constraints,
        subst,
        tipo,
        scheme,
        engine,
    })
}

#[cfg(test)]
mod tests {

    #[test]
    fn it_works() {
        assert_eq!(2 + 2, 4);
        println!("{}", std::mem::size_of::<u32>());
        println!("{}", std::mem::size_of::<i64>())
    }
}
