use std::borrow::Borrow;

use crate::{
    envr::Envr,
    infer::{Constraint, Infer, Solve, Unifier},
    literal::{Lit, Literal},
    name::Name,
    subst::{Subst, Substitutable},
    types::{Scheme, Type},
};

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Expression<T> {
    Ident(T),
    Lit(Literal),
    List(Vec<Expression<T>>),
    Tuple(Vec<Expression<T>>),
    Lam(T, Box<Expression<T>>),
    App(Box<Expression<T>>, Box<Expression<T>>),
    Let(T, Box<Expression<T>>, Box<Expression<T>>),
    Bin(PrimOp, Box<Expression<T>>, Box<Expression<T>>),
    Cond(Box<Expression<T>>, Box<Expression<T>>, Box<Expression<T>>),
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Declaration<T>(pub T, pub Expression<T>);

pub type Expr = Expression<Name>;
pub type Decl = Declaration<Name>;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum PrimOp {
    Add,
    Sub,
    Mul,
    NotEq,
    Eq,
    Less,
    Greater,
    LessEq,
    GreaterEq,
}

impl PrimOp {
    /// Primitive op return types. Simplified for the time being.
    pub fn ret_ty(self) -> Type {
        match self {
            PrimOp::Add | PrimOp::Sub | PrimOp::Mul => Type::INT,
            PrimOp::NotEq
            | PrimOp::Eq
            | PrimOp::Less
            | PrimOp::Greater
            | PrimOp::LessEq
            | PrimOp::GreaterEq => Type::BOOL,
        }
    }

    pub fn signature(self, engine: &mut Infer) -> Type {
        use PrimOp::*;
        match self {
            Add | Sub | Mul => Type::Lam(
                Type::INT.boxed(),
                Type::Lam(Type::INT.boxed(), Type::INT.boxed()).boxed(),
            ),
            NotEq | Eq | Less | Greater | LessEq | GreaterEq => {
                let a = engine.fresh();
                let b = engine.fresh();
                Type::Lam(a.boxed(), Type::Lam(b.boxed(), Type::BOOL.boxed()).boxed())
            }
        }
    }

    pub fn as_str(self) -> &'static str {
        match self {
            PrimOp::Add => "+",
            PrimOp::Sub => "-",
            PrimOp::Mul => "*",
            PrimOp::NotEq => "!=",
            PrimOp::Eq => "==",
            PrimOp::Less => "<",
            PrimOp::Greater => ">",
            PrimOp::LessEq => "<=",
            PrimOp::GreaterEq => ">=",
        }
    }
}
