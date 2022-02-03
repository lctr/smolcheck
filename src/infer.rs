use std::{collections::HashMap, fmt::Debug};

use crate::{
    constraint::Constraint,
    envr::Envr,
    expr::{Decl, Declaration, Expr, Expression},
    failure::{Failure, Solve},
    name::{Fresh, Name, SymId, Ty},
    subst::{Subst, Substitutable},
    types::{Scheme, Type},
    unify::Unifier,
};

use crate::types::constants::*;

impl Fresh for Infer {
    type Repr = Type;

    fn fresh(&mut self) -> Self::Repr {
        Self::fresh(self)
    }
}

#[derive(Clone, Debug, Default)]
pub struct Infer {
    pub count: SymId,
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
        let count = self.count;
        self.count += 1;
        Type::Var(Ty(count))
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
        let t_ftv = ty.ftv();
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

    pub fn infer_bindings(&mut self, items: &[(Name, Expr)]) -> Solve<&mut Self> {
        match items {
            [] => Ok(self),
            [(name, expr), rest @ ..] => {
                let sch = self.infer_expr_scheme(expr)?;
                self.envr.insert(*name, sch);
                self.infer_bindings(rest)
            }
        }
    }

    pub fn infer_expr_scheme(&mut self, expr: &Expr) -> Solve<Scheme> {
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
                        let tv2 = self.fresh();
                        Ok((Type::List(tv.box_cloned()), vec![(tv2, tv).into()]))
                    }
                    [x] => {
                        let tv = self.fresh();
                        let (c, sub, t, sc) = self.constraints_expr(x)?;
                        let u1 = Type::List(tv.boxed());
                        let u2 = Type::List(t.clone().boxed());
                        let cs = c
                            .into_iter()
                            .chain([(Type::List(t.boxed()), u1).into()])
                            .collect();
                        Ok((u2, cs))
                    }
                    xs => {
                        let (c, sub, t, sc) = self.constraints_expr(&Expr::List(vec![]))?;
                        let _t = t.clone();

                        let (cs, subst, ty, _scheme) =
                            xs.iter().fold(Ok((c, sub, t, sc)), |a, x| {
                                let (acs, asub, at, _asch) = a?;
                                if acs.iter().any(|Constraint(t1, t2)| match (t1, t2) {
                                    (Type::Lit(l1), Type::Lit(l2)) => l1 != l2,
                                    _ => false,
                                }) {
                                    let (l, r) = vec![Constraint(_t.clone(), at)]
                                        .into_iter()
                                        .chain(acs)
                                        .fold(
                                            (vec![], vec![]),
                                            |(mut al, mut ar), Constraint(cx, cy)| {
                                                al.push(cx);
                                                ar.push(cy);
                                                (al, ar)
                                            },
                                        );
                                    return Err(Failure::Mismatch(l, r));
                                };

                                let (c1, s1, t1, sch) = self.constraints_expr(x)?;
                                let s2 = s1.compose(&asub);
                                let tipo = self.instantiate(&sch.normalize()?)?.apply(&s2);

                                if at.ftv().is_empty() && tipo.ftv().is_empty() {
                                    if at == tipo {
                                        let sch = at.generalize(&self.envr);
                                        return Ok((c1, s2, tipo, sch));
                                    } else {
                                        return Err(Failure::NotUnified(at, tipo));
                                    }
                                };

                                let cs = vec![
                                    acs,
                                    c1,
                                    vec![Constraint(t1, at.clone()), Constraint(at, tipo.clone())],
                                ]
                                .into_iter()
                                .flatten()
                                .collect();
                                let sch = sch.apply(&s2);
                                Ok((cs, s2, tipo, sch))
                            })?;

                        Ok((Type::List(ty.apply(&subst).boxed()), cs))
                    }
                }
            }
            Expression::Tuple(xs) => {
                if xs.is_empty() {
                    Ok((UNIT, vec![]))
                } else {
                    let init = (vec![], vec![]);
                    let (ts, cs) = xs
                        .iter()
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

                self.envr.insert(*x, Scheme::monotype(tv.clone()));
                let (t, c) = self.infer(e.as_ref())?;
                Ok((Type::Lam(tv.boxed(), t.boxed()), c))
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
                let cs = vec![c1, c2, c3, vec![(t1, BOOL).into(), (t2.clone(), t3).into()]]
                    .into_iter()
                    .flatten()
                    .collect::<Vec<_>>();
                Ok((t2, cs))
            }
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
            let solved = Unifier::solve(sub, &cs);
            match solved {
                Ok(soln) => {
                    println!("solution sub: {}", &soln);
                    println!("sub applied: {}", ty.apply(&soln))
                }
                Err(e) => println!("{}", e),
            }
        }
        Err(e) => println!("{}", e),
    };
    println!("Type Environment: {:#?}", &engine.envr)
}

#[cfg(test)]
mod test {
    use crate::{expr::PrimOp, literal::Literal};

    use super::*;

    #[test]
    fn inspect_nil() {
        let nil = Expr::List(vec![]);
        let nilsrc = "[]";
        t_run_show(nilsrc, &nil);
    }

    fn lit_list(xs: &[Literal]) -> Expr {
        Expr::List(xs.iter().map(|x| Expr::Lit(x.clone())).collect::<Vec<_>>())
    }

    #[test]
    fn test_reject_bad_list() {
        let bad_list = &[Literal::Int(1), Literal::Char('s')];
        let bad_list_source = "[1, 's']";
        let bad_list = lit_list(bad_list);
        t_run_show(bad_list_source, &bad_list);
        assert_eq!(
            Infer::new().infer(&bad_list),
            Err(Failure::NotUnified(INT, CHAR))
        );
    }

    #[test]
    fn test_list() {
        let list1 = Expr::List((1..10).map(|n| Expr::Lit(Literal::Int(n))).collect());
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

        let src = "`\\x -> x + 5`";
        t_run_show(src, &lam);
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
        fn mk_tuple(seed: usize, lim: usize, bases: &[Type]) -> Type {
            let _base = &[BOOL, Type::Var(Ty(0)), CHAR, UNIT, Type::List(INT.boxed())][..];
            let bases = if bases.is_empty() { _base } else { bases };
            let len = bases.len();
            Type::Tuple(
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
                            Type::Lam(
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
        let tup0 = Type::Tuple((0..lim as u32).map(|i| Type::Var(Ty(i))).collect());
        let tup1 = mk_tuple(3, lim, &[]);
        let tup2 = mk_tuple(
            3,
            lim,
            &[Type::List(Type::Tuple(vec![CHAR, INT, INT]).boxed())],
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
