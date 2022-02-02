mod constraint;
mod envr;
mod expr;
mod failure;
mod infer;
mod literal;
mod name;
mod subst;
mod types;
mod unify;

pub trait Hashy: Clone + Eq + std::hash::Hash {}

impl<T> Hashy for T where T: Clone + Eq + std::hash::Hash {}

#[cfg(test)]
mod tests {

    #[test]
    fn it_works() {
        assert_eq!(2 + 2, 4);
        println!("{}", std::mem::size_of::<u32>());
        println!("{}", std::mem::size_of::<i64>())
    }
}
