#[derive(Clone, Debug)]
pub struct Many<'a, A, S>(pub &'a [A], pub S);

impl<'a, A, S> std::fmt::Display for Many<'a, A, S>
where
    A: std::fmt::Display,
    S: std::fmt::Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.0[..] {
            [] => Ok(()),
            [a] => A::fmt(a, f),
            [ref head, rest @ ..] => {
                let sep = &self.1;
                let init = A::fmt(head, f);
                rest.iter().fold(init, |_, c| {
                    S::fmt(sep, f)?;
                    A::fmt(c, f)?;
                    Ok(())
                })
            }
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn print_many() {
        println!("{}", Many(&[1, 2, 3, 4], ", "))
    }
}
