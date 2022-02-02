use std::borrow::Borrow;

use crate::{
    constraint::Constraint,
    envr::Envr,
    failure::Solve,
    infer::Infer,
    literal::{Lit, Literal},
    name::Name,
    subst::{Subst, Substitutable},
    types::{Scheme, Type},
    unify::Unifier,
    Hashy,
};

pub enum Kind<T>{
    Hash(T),
    Star(T),
    Arrow(Box<Kind<T>>, Box<Kind<T>>)
}

/// An expression is a generic enum that represents the nodes of an abstract
/// syntax tree. In this implementation, expressions may be parametrized by
/// the types of the containers for literal types, identifier types, and infix
/// operator (identifier) types.
///
/// # Example
/// Let's decribe how the expression `x + 1` is represented in order to
/// quantify the type parameters involved.
///
/// ## Regarding literals `L`
/// Suppose we define a type `Literal` to contain any instances
/// of types carrying parsed literal data so that said parsed literal data
/// corresponded to the primitive types `(), Int, Bool, Char, Str`.
///
/// ## Regarding tokens `T`
/// We may decide to represent variable names directly, in which case the use
/// of the descriptor "tokens" takes on a literal meaning. However, suppose not
/// only are we interning all of our identifiers -- and thus, for some stored,
/// string or text-like type `S`, its representation can be retrieved with the
/// corresponding key of type `T`.
///
/// ```
/// // A trivial example of an 'interner' highlighting roles of `S` and `T`
/// let mut interner = vec![(0, "a"), (1, "cat"), (2, "y"), (3, "+")];
/// let identifier = Name::Lower(2);
/// let ident_node = Expression::Ident(identifier);
/// ```
///
///
/// were to distinguish between identifiers beginning with an uppercase letter
/// vs one beginning with a lowercase letter. Additionally, we'll allow for
/// a variant that lets us directly represent a static string slice. The only
/// thing missing now is a variant that will facilitate safely renaming
/// identifiers
///
/// ```
/// #[derive(Copy, Clone)]
/// enum Name { Lower(K), Upper(K), Display(&'static str) }
/// ```
///
/// ## Regarding `O`
///
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Expression<T, O> {
    Ident(T),
    Lit(Literal),
    List(Vec<Expression<T, O>>),
    Tuple(Vec<Expression<T, O>>),
    Lam(T, Box<Expression<T, O>>),
    App(Box<Expression<T, O>>, Box<Expression<T, O>>),
    Let(T, Box<Expression<T, O>>, Box<Expression<T, O>>),
    Bin(O, Box<Expression<T, O>>, Box<Expression<T, O>>),
    Cond(
        Box<Expression<T, O>>,
        Box<Expression<T, O>>,
        Box<Expression<T, O>>,
    ),
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Declaration<T>(pub T, pub Expression<T, PrimOp>);

pub type Expr = Expression<Name, PrimOp>;
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
    Or,
    And,
}

pub trait Signature {
    type Repr: Hashy;
    type Context;

    fn signature(self, context: &mut Self::Context) -> Self::Repr;
}

impl PrimOp {
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
            Or | And => Type::Lam(
                Type::BOOL.boxed(),
                Type::Lam(Type::BOOL.boxed(), Type::BOOL.boxed()).boxed(),
            ),
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
            PrimOp::Or => "||",
            PrimOp::And => "&&",
        }
    }
}
