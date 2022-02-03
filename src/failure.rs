use crate::{constraint::Constraint, name::Name, types::Type};

pub type Solve<T> = Result<T, Failure>;

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
            Failure::NotUnified(Type::Lit(x), Type::Lit(y)) => write!(
                f,
                "distinct primitives! Unable to unify the primitive `{}` with `{}`",
                x, y
            ),
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
                for Constraint(x, y) in cs {
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
