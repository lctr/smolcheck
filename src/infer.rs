use std::{
    collections::{HashMap, HashSet},
    fmt::{Debug, Pointer},
};

use crate::{
    envr::Envr,
    expr::{Decl, Declaration, Expr, Expression},
    name::{Name, Sym, Var},
    subst::{occurs_check, Subst, Substitutable},
    types::{Many, Scheme, Type},
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

#[derive(Clone, Debug, Default)]
pub struct Infer {
    pub count: Sym,
    pub envr: Envr,
}

impl Infer {
    pub fn new() -> Infer {
        Infer::default()
    }

    pub fn with_predefined(bases: Vec<(Name, Scheme)>) -> Infer {
        let envr = Envr::with_entries(bases);
        Infer { count: 0, envr }
    }

    pub fn fresh(&mut self) -> Type {
        let count = self.count.clone();
        self.count += 1;
        Type::Var(Var(count))
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
                // first infer the operand types
                let (t1, c1) = self.infer(left.as_ref())?;
                let (t2, c2) = self.infer(right.as_ref())?;
                let tv = self.fresh();
                // generate the expected type to be on of the overall
                // type's constraints
                // binary operations are typed as functions
                let u1 = Type::Lam(
                    Box::new(t1),
                    Box::new(Type::Lam(Box::new(t2), Box::new(tv.clone()))),
                );
                // Todo: parametrize!!!! expected return type of operator
                // let u2 = op.ret_ty();
                let u2 = op.signature(self);
                // constraints for all types involved
                let cs = vec![c1, c2, vec![(u1, u2).into()]]
                    .into_iter()
                    .flatten()
                    .collect::<Vec<_>>();
                Ok((tv, cs))
            }
            Expression::List(a) => {
                match &a[..] {
                    // empty list has type `[a]` for some type `a`
                    [] => {
                        let tv = self.fresh();
                        let ty = Type::List(tv.clone().boxed());
                        // let tv2 = self.fresh();
                        Ok((Type::List(ty.clone().boxed()), vec![(ty, tv).into()]))
                    }
                    [x] => {
                        let tv = self.fresh();
                        let (t, c) = self.infer(x)?;
                        let u1 = Type::List(tv.clone().boxed());
                        let u2 = Type::List(t.clone().boxed());
                        let cs = c.into_iter().chain([(t, u1).into()]).collect();
                        Ok((u2, cs))
                    }
                    xs => {
                        let tv = self.fresh();
                        let c0s: Vec<Constraint> = vec![];
                        let (ty, cs) = xs
                            .into_iter()
                            .map(|x| {
                                let tvi = self.fresh();
                                let (ty, mut cs) = self.infer(x)?;
                                cs.push(Constraint(ty.clone(), tvi.clone()));
                                cs.push(Constraint(tvi.clone(), tv.clone()));
                                Ok((ty, cs))
                            })
                            .fold(Ok((tv.clone(), c0s)), |a, c| {
                                let (at, mut acs) = a?;
                                let (ct, cts) = c?;
                                acs.extend(cts);
                                acs.push(Constraint(ct.clone(), at));
                                Ok((ct, acs))
                            })?;
                        Ok((Type::List(ty.boxed()), cs))
                    }
                }
            }
            Expression::Tuple(xs) => {
                if xs.is_empty() {
                    Ok((Type::UNIT, vec![]))
                } else {
                    let init = (vec![], vec![]);
                    let (ts, cs) = xs
                        .into_iter()
                        .map(|x| {
                            let tv = self.fresh();
                            let (ty, mut cs) = self.infer(x)?;
                            cs.push(Constraint(ty.clone(), tv));
                            Ok((ty, cs))
                        })
                        .fold(Ok(init), |a, c| {
                            let (tyi, cis) = c?;
                            let (mut tys, mut cts) = a?;
                            tys.push(tyi);
                            cts.extend(cis);
                            Ok((tys, cts))
                        })?;
                    Ok((Type::Tuple(ts), cs))
                }
            }
            Expression::Lam(x, e) => {
                let tv = self.fresh();
                // self.envr.remove(x);
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
                let constraints = vec![
                    c1,
                    c2,
                    vec![(t1, Type::Lam(Box::new(t2), Box::new(tv.clone()))).into()],
                ]
                .into_iter()
                .flatten()
                .collect::<Vec<_>>();
                Ok((tv, constraints))
            }
            Expression::Let(x, e1, e2) => {
                let (bound_ty, bound_constraints) = self.infer(e1.as_ref())?;
                let sub = Unifier::solve(Subst::empty(), &bound_constraints)?;
                let mut ctx = self.envr.apply(&sub);
                let ty = bound_ty.apply(&sub);
                let sch = ty.generalize(&ctx);
                // let-
                let mut eng2 = self.clone();
                ctx.insert(*x, sch);
                eng2.envr = ctx.apply(&sub);
                let (t2, c2) = eng2.infer(e2.as_ref())?;
                let tipo = t2;
                let cs = bound_constraints.into_iter().chain(c2).collect();
                Ok((tipo, cs))
            }
            Expression::Cond(cond, then, other) => {
                let (t1, c1) = self.infer(cond.as_ref())?;
                let (t2, c2) = self.infer(then.as_ref())?;
                let (t3, c3) = self.infer(other.as_ref())?;
                let cs = vec![
                    c1,
                    c2,
                    c3,
                    vec![(t1, Type::BOOL).into(), (t2.clone(), t3).into()],
                ]
                .into_iter()
                .flatten()
                .collect::<Vec<_>>();
                Ok((t2, cs))
            }
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Constraint(pub Type, pub Type);

impl Constraint {
    pub fn ppr_slice(cs: &[Constraint]) {
        for c in cs {
            println!("\t{}", c);
        }
    }
}

impl From<(Type, Type)> for Constraint {
    fn from((t1, t2): (Type, Type)) -> Self {
        Constraint(t1, t2)
    }
}

impl std::fmt::Display for Constraint {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "({}, {})", &self.0, &self.1)
    }
}

impl Substitutable for Constraint {
    fn ftv(&self) -> HashSet<Var> {
        let fvs1 = self.0.ftv();
        let fvs2 = &self.1.ftv();
        fvs1.union(fvs2).cloned().collect()
    }

    fn apply(&self, sub: &Subst) -> Self {
        let Constraint(t1, t2) = self;
        Constraint(t1.apply(sub), t2.apply(sub))
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
        Unifier::new(sub, constraints.to_vec()).solver()

        // let cs = constraints;
        // match cs.split_first() {
        //     Some((head, rest)) => {
        //         let Constraint(t1, t2) = head.clone();
        //         let s1 = Self::unifies(t1, t2)?;
        //         let s2 = s1.compose(&sub);
        //         let tail = rest.to_vec().apply(&s1);
        //         Self::solve(s2, tail.as_slice())
        //     }
        //     None => Ok(sub),
        // }
    }

    fn solver(self) -> Solve<Subst> {
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
                (Type::Con(x), Type::Con(y)) if x == y => Ok(Subst::empty()),
                (Type::Var(v), t) => Self::bind(v, t),
                (t, Type::Var(v)) => Self::bind(v, t),
                (Type::Lam(x1, y1), Type::Lam(x2, y2)) => {
                    Self::unify_many(&[*x1, *y1], &[*x2, *y2])
                }
                (Type::List(x), Type::List(y)) => Self::unifies(*x, *y),
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

    pub fn bind(var: Var, ty: Type) -> Solve<Subst> {
        match ty {
            Type::Var(v) if v == var => Ok(Subst::empty()),
            t if occurs_check(&t, var) => Err(Failure::Infinite(t, Type::Var(var))),
            _ => Ok(Subst::singleton(var, ty)),
        }
    }
}

fn t_run_show(source: &str, expr: &Expr) {
    let mut engine = Infer::new();
    println!("source: {}", &source);
    match engine.infer(expr) {
        Ok(res) => {
            println!(".infer() results");
            println!("  type:\n\t{}", &res.0);
            println!("  constraints:");
            Constraint::ppr_slice(res.1.as_slice())
        }
        Err(e) => println!("{}", e),
    };
    match engine.constraints_expr(expr) {
        Ok(res) => {
            println!(".constraints_expr() results");
            let (cs, sub, ty, scheme) = res;
            println!("  constraints:");
            Constraint::ppr_slice(cs.as_slice());
            println!("  substitution: {}", &sub);
            println!("  type:\n\t{}", &ty);
            println!("  scheme:\n\t{}", &scheme);
        }
        Err(e) => println!("{}", e),
    };
}

#[cfg(test)]
mod test {
    use crate::{expr::PrimOp, literal::Literal};

    use super::*;

    #[test]
    fn test_list() {
        fn lit_list(xs: &[Literal]) -> Expr {
            Expr::List(xs.iter().map(|x| Expr::Lit(x.clone())).collect::<Vec<_>>())
        }

        let bad_list = &[Literal::Int(1), Literal::Char('s')];
        let bad_list_source = "[1, 's']";
        let bad_list = lit_list(bad_list);
        t_run_show(bad_list_source, &bad_list);

        let list1 = Expr::List((1..10).map(|n| Expr::Lit(Literal::Int(5))).collect());
        let src1 = "[1, 2, 3, 4, 5, 6, 7, 8, 9]";
        t_run_show(src1, &list1);

        let lam = Expr::Lam(
            Name::Named("x"),
            Box::new(Expr::List(vec![Expr::Bin(
                PrimOp::Add,
                Box::new(Expr::Ident(Name::Named("x"))),
                Box::new(Expr::Lit(Literal::Int(5))),
            )])),
        );
        let src2 = "\\x -> [x + 5]";
        t_run_show(src2, &lam);

        let list = Expr::List(vec![list1.clone()]);
        let src3 = format!("[{}]", &src1);
        t_run_show(&*src3, &list)
    }

    #[test]
    fn test_infer_lambda() {
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
            Ok(res) => {
                println!(".infer() results");
                println!("  type:\n\t{}", &res.0);
                println!("  constraints:");
                Constraint::ppr_slice(res.1.as_slice())
            }
            Err(e) => println!("{}", e),
        };
        match checker.constraints_expr(&lam) {
            Ok(res) => {
                println!(".constraints_expr() results");
                let (cs, sub, ty, scheme) = res;
                println!("  constraints:");
                Constraint::ppr_slice(cs.as_slice());
                println!("  substitution: {}", &sub);
                println!("  type:\n\t{}", &ty);
                println!("  scheme:\n\t{}", &scheme);
                println!("  substitution applied to type:\n\t{}", ty.apply(&sub));
            }
            Err(e) => println!("{}", e),
        };
    }

    #[test]
    fn inspect_infer_let() {
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
        let llet = Expr::Let(
            Name::Named("x"),
            Box::new(Expr::Lit(Literal::Int(4))),
            Box::new(cond),
        );

        let source = "let x = 4 in if x == 5 then 10 else x + 10";
        t_run_show(source, &llet);
    }

    #[test]
    fn test_unify_zip_vs_many() {
        use Type as Ty;

        fn mk_tuple(seed: usize, lim: usize, bases: &[Type]) -> Type {
            let _base = &[
                Ty::BOOL,
                Ty::Var(Var(0)),
                Ty::CHAR,
                Ty::UNIT,
                Ty::List(Ty::INT.boxed()),
            ][..];
            let bases = if bases.is_empty() { _base } else { bases };
            let len = bases.len();
            Ty::Tuple(
                // bases.chain(bases.iter().rev())
                bases
                    .iter()
                    .zip(bases.iter().rev().chain(_base))
                    .cycle()
                    .step_by(len + 1)
                    .take(lim)
                    .enumerate()
                    .map(|(i, (t1, t2))| {
                        if let Some(d) = lim.checked_rem_euclid(len) {
                            Ty::Lam(
                                t1.clone().boxed(),
                                bases[((d + i) % len).min(i)].clone().boxed(),
                            )
                            .clone()
                        } else {
                            (if i % 2 == 0 { t1 } else { t2 }).clone()
                        }
                    })
                    .fold(vec![], |mut a, c| {
                        a.push(c);
                        a
                    }),
            )
        }

        let lim = 9;
        let tup0 = Ty::Tuple((0..lim as u32).map(|i| Ty::Var(Var(i))).collect());
        let tup1 = mk_tuple(3, lim, &[]);
        let tup2 = mk_tuple(
            3,
            lim,
            &[Ty::List(
                Ty::Tuple(vec![Ty::CHAR, Ty::INT, Ty::INT]).boxed(),
            )],
        );
        println!("tup0 :: {}", &tup0);
        println!("tup1 :: {}", &tup1);
        println!("tup2 :: {}", &tup2);
        print!("unifying tup0 with tup1: ");
        match Unifier::unifies(tup0, tup1.clone()) {
            Ok(sub) => {
                print!("{}", &sub);
                let envr1 = Envr::new().apply(&sub);

                println!("tup1 generalized (type scheme)");
                let sc = tup1.generalize(&envr1);
                println!("\t{}", sc);
            }
            Err(e) => print!("{}", e),
        };

        let tup = Expr::Tuple(vec![
            Expr::Lit(Literal::Bool(true)),
            Expr::Lit(Literal::Char('c')),
            Expr::List(
                (1..6i32)
                    .map(|i| Expr::Lit(Literal::Int(i)))
                    .collect::<Vec<_>>(),
            ),
        ]);
        let source = "(True, 'c', [1, 2, 3, 4, 5])";

        t_run_show(source, &tup);
    }
}
