use std::marker::PhantomData;

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum Lit {
    Unit,
    Bool,
    Int,
    Float,
    Double,
    Char,
    Str,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
/// A utility intermediary type providing a link between potentially
/// different `Literal` types, e.g., from a different crate, etc.
///
/// Define the following utility shorthand to denote an instance of the
/// type `Primitive<X, N>` for some type `X` and some `const N usize`:
///
///     P(X, N) ::= Primitive<X, n as usize>(x, PhantomData<[X; N]>);
///
/// Then a primitive `P` must satisfy the following rules for applying
/// a function `f` to `P`:
/// * `f P((), 0) = f ()`
/// * `f P(bool, 1) = f (b :: Bool)`
/// * `f P(i32, 1) = f (i :: Int)`
/// * `f P(char, 1) = f (c :: Char)`
/// * `f P(&'static str, 1) = f (s :: Str)`
///
/// A primitive `P` also dereferences to their contained value, so it follows
/// the contained value `T` *must* be sized (though this is not strictly
/// required for existence, it is required when looking to dereference to
/// `T`).
///
/// While other type combinations are free to exist, they run the risk of
/// not being properly typechecked without manual intervention.
pub struct Primitive<T, const N: usize>(T, PhantomData<[T; N]>);

impl<T> From<bool> for Primitive<T, 1>
where
    T: From<bool>,
{
    fn from(b: bool) -> Self {
        Primitive::<T, 1>(b.into(), PhantomData)
    }
}

#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash, Default)]
pub struct Rational<Z> {
    int: Z,
    frac: Z,
}

impl<Z> Rational<Z> {
    pub fn new(int: Z, frac: Z) -> Rational<Z> {
        Rational { int, frac }
    }
}

impl Rational<u32> {
    pub fn value(&self) -> f32 {
        f32::hypot(self.int as f32, self.frac as f32)
    }
}

pub fn f64_mantissa_exp_sgn(float: f64) -> (u64, i16, i8) {
    #![allow(unused)]

    let bits: u64 = float.to_bits();
    let sign: i8 = if bits >> 63 == 0 { 1 } else { -1 };
    let mut exp: i16 = ((bits >> 52) & 0x7ff) as i16;
    let mantissa = if exp == 0 {
        (bits & 0xfffffffffffff) << 1
    } else {
        (bits & 0xfffffffffffff) | 0x10000000000000
    };
    exp -= 1023 + 52;
    (mantissa, exp, sign)
}

impl<T, const N: usize> std::ops::Deref for Primitive<T, N>
where
    T: Sized,
{
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &(self.0)
    }
}

#[test]
fn print_prim_size() {
    let sizes = &[
        std::mem::size_of::<Primitive<(), 0>>(),
        std::mem::size_of::<Primitive<bool, 1>>(),
        std::mem::size_of::<Primitive<i32, 1>>(),
        std::mem::size_of::<Primitive<char, 1>>(),
        std::mem::size_of::<Primitive<&'static str, 1>>(),
    ];
    for n in sizes {
        println!("{}", n)
    }
}

pub type Float = Rational<u32>;
pub type Double = Rational<u64>;

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum Literal {
    Unit,
    Bool(bool),
    Int(i32),
    Float(Float),
    Double(Double),
    Char(char),
    Str(&'static str),
}

impl std::fmt::Display for Lit {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if matches!(self, Self::Unit) {
            write!(f, "()")
        } else {
            write!(f, "{:?}", &self)
        }
    }
}

impl From<Literal> for Lit {
    fn from(m: Literal) -> Self {
        match m {
            Literal::Unit => Self::Unit,
            Literal::Bool(_) => Self::Bool,
            Literal::Int(_) => Self::Int,
            Literal::Float(_) => Self::Float,
            Literal::Double(_) => Self::Double,
            Literal::Char(_) => Self::Char,
            Literal::Str(_) => Self::Str,
        }
    }
}

#[cfg(test)]
mod test {
    use super::{Lit, Literal};

    #[test]
    fn size_of_lit() {
        println!("|lit| = {}", std::mem::size_of::<Lit>())
    }

    #[test]
    fn size_of_literal() {
        println!("|literal| = {}", std::mem::size_of::<Literal>())
    }
}
