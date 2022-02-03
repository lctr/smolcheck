use crate::{
    failure::Solve,
    infer::Infer,
    literal::{Lit, Literal},
    name::{Name, SymId},
    types::{constants::*, Type},
    Hashy,
};

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
pub enum Expression<L, T, O> {
    Ident(T),
    Lit(L),
    List(Vec<Expression<L, T, O>>),
    Tuple(Vec<Expression<L, T, O>>),
    Lam(T, Box<Expression<L, T, O>>),
    App(Box<Expression<L, T, O>>, Box<Expression<L, T, O>>),
    Let(T, Box<Expression<L, T, O>>, Box<Expression<L, T, O>>),
    Bin(O, Box<Expression<L, T, O>>, Box<Expression<L, T, O>>),
    Cond(
        Box<Expression<L, T, O>>,
        Box<Expression<L, T, O>>,
        Box<Expression<L, T, O>>,
    ),
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Declaration<L, T, O>(pub T, pub Expression<L, T, O>);

pub type Expr = Expression<Literal, Name, PrimOp>;
pub type Decl = Declaration<Literal, Name, PrimOp>;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum PrimOp {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
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
        use PrimOp as P;
        match self {
            P::Div => Type::Lam(
                engine.fresh().boxed(),
                Type::Lam(engine.fresh().boxed(), Type::Lit(Lit::Float).boxed()).boxed(),
            ),
            P::Add | P::Sub | P::Mul | P::Rem => Type::Lam(
                Type::INT.boxed(),
                Type::Lam(Type::INT.boxed(), Type::INT.boxed()).boxed(),
            ),
            P::NotEq | P::Eq | P::Less | P::Greater | P::LessEq | P::GreaterEq => {
                let a = engine.fresh();
                let b = engine.fresh();
                Type::Lam(a.boxed(), Type::Lam(b.boxed(), Type::BOOL.boxed()).boxed())
            }

            P::Or | P::And => Type::Lam(
                Type::BOOL.boxed(),
                Type::Lam(Type::BOOL.boxed(), Type::BOOL.boxed()).boxed(),
            ),
        }
    }

    pub fn base_infixes(self, left: Type, right: Type) -> Solve<Type> {
        fn lam(t1: Type, t2: Type, t3: Type) -> Type {
            Type::Lam(t1.boxed(), Type::Lam(t2.boxed(), t3.boxed()).boxed())
        }

        use super::Lit as L;
        use Type as T;
        match (self, (left, right)) {
            (PrimOp::Add | PrimOp::Sub | PrimOp::Mul | PrimOp::Rem, (T::Lit(l), T::Lit(r)))
                if l == r && matches!(l, L::Int | L::Float | L::Double) =>
            {
                Ok(lam(T::Lit(l), T::Lit(r), T::Lit(l)))
            }
            (PrimOp::Div, (T::Lit(l), T::Lit(r)))
                if l == r && matches!(l, L::Float | L::Double) =>
            {
                Ok(lam(T::Lit(l), T::Lit(r), T::Lit(l)))
            }
            (
                PrimOp::Less
                | PrimOp::Greater
                | PrimOp::Eq
                | PrimOp::NotEq
                | PrimOp::GreaterEq
                | PrimOp::LessEq,
                (T::Lit(l), T::Lit(r)),
            ) if l == r => Ok(lam(T::Lit(l), T::Lit(r), BOOL)),
            (PrimOp::Or | PrimOp::And, (ref t @ T::Lit(l), ref r))
                if t == r && matches!(l, L::Bool) =>
            {
                Ok(lam(BOOL, BOOL, BOOL))
            }
            _ => {
                todo!()
            }
        }
    }

    pub fn as_str(self) -> &'static str {
        match self {
            PrimOp::Add => "+",
            PrimOp::Sub => "-",
            PrimOp::Mul => "*",
            PrimOp::Div => "/",
            PrimOp::Rem => "%",
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

pub trait InfixRule {
    type Key;
    type Value;
    type Infix;
    type Engine;

    fn get_id(&self) -> &Self::Key;

    fn sym_id(&self) -> SymId;

    /// Lookup the type scheme corresponding to the `self` infix as a name
    /// in the type environment `engine`.
    fn lookup_name(engine: &Self::Engine) -> Option<&Self::Value>;
}
