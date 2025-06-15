use std::cell::RefCell;
use std::collections::HashMap;
use std::fmt::{Display, Formatter, Write};
use std::ops::{Range, Add, Deref};
use std::rc::Rc;
use std::iter::{self, FromIterator};

use anyhow::bail;
use imbl::{vector, HashSet, Vector};
use indenter::indented;
use itertools::Itertools;
use num::ToPrimitive;
use z3::ast::{exists_const, Ast, Bool, Dynamic, Int, Real as Re, String as Str};
use z3::{Config, Context, Solver, Sort};

use super::shared::{Ctx, Lambda, Sigma, Typed};
use super::stable::{self, stablize};
use super::unify::{Unify, UnifyEnv};
use crate::pipeline::relation::{num_cmp, num_op};
use crate::pipeline::relation as rel;
use crate::pipeline::shared::{DataType, Eval, Neutral as Neut, Terms, VL};
use crate::pipeline::shared::Schema;
use crate::pipeline::{partial, shared};
use crate::pipeline::constraint;

pub type Relation = Lambda<UExpr>;

pub type Expr = shared::Expr<UExpr, Relation, Aggr>;
pub type Neutral = shared::Neutral<Relation, Expr>;
pub type Head = shared::Head<Relation, Expr>;
pub type Logic = shared::Logic<UExpr, Expr>;

pub type Term = Sigma<Inner>;
pub type UExpr = Terms<Term>;

impl UExpr {
	pub fn under(scope: Vector<DataType>, terms: UExpr) -> Self {
		terms.into_iter().map(|term| Sigma(scope.clone() + term.0, term.1)).collect()
	}
}

#[derive(Clone, Debug, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct Aggr(pub String, pub Vector<DataType>, pub Box<Inner>, pub Box<Expr>);

impl Display for Aggr {
	fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
		let Aggr(name, scope, uexpr, expr) = self;
		writeln!(f, "⨿{} {:?} {{", name, scope)?;
		writeln!(indented(f).with_str("\t"), "{},", uexpr)?;
		writeln!(indented(f).with_str("\t"), "{}", expr)?;
		write!(f, "}}")
	}
}

impl Typed for Aggr {
	fn ty(&self) -> DataType {
		self.3.ty()
	}
}

impl Aggr {
	pub fn under(scope: Vector<DataType>, aggs: Vector<Aggr>) -> Vector<Aggr> {
		aggs.into_iter().map(|Aggr(op, scp, u, e)| Aggr(op, scope.clone() + scp, u, e)).collect()
	}
}

#[derive(Clone, Debug, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct Inner {
	pub logic: Logic,
	pub apps: Vector<Neutral>,
}

impl Display for Inner {
	fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
		write!(f, "⟦{}⟧ × ({})", self.logic, self.apps.iter().format(" × "))
	}
}

impl Inner {
	pub(crate) fn in_scope(&self, lvl: usize) -> bool {
		self.logic.in_scope(lvl) && self.apps.iter().all(|app| app.in_scope(lvl))
	}
}

impl Aggr {
	pub(crate) fn deps(&self, vars: &Range<usize>) -> HashSet<VL> {
		let Aggr(_, _, u, e) = self;
		e.deps(vars) + u.logic.deps(vars) + HashSet::unions(u.apps.iter().map(|app| app.deps(vars)))
	}

	pub(crate) fn in_scope(&self, lvl: usize) -> bool {
		let Aggr(_, scope, u, e) = self;
		u.in_scope(lvl + scope.len()) && e.in_scope(lvl + scope.len())
	}
}

impl Expr {
	pub(crate) fn deps(&self, vars: &Range<usize>) -> HashSet<VL> {
		match self {
			Expr::Var(v, _) if vars.contains(&v.0) => HashSet::unit(*v),
			Expr::Var(_, _) => HashSet::new(),
			Expr::Log(l) => l.deps(vars),
			Expr::Agg(agg) => agg.deps(vars),
			Expr::Op(_, args, _) => HashSet::unions(args.iter().map(|arg| arg.deps(vars))),
			Expr::HOp(_, args, rel, _) => {
				HashSet::unions(args.iter().map(|arg| arg.deps(vars))) + rel.deps(vars)
			},
		}
	}

	pub(crate) fn in_scope(&self, lvl: usize) -> bool {
		match self {
			Expr::Var(VL(l), _) => *l < lvl,
			Expr::Log(l) => l.in_scope(lvl),
			Expr::Agg(agg) => agg.in_scope(lvl),
			Expr::Op(_, args, _) => args.iter().all(|arg| arg.in_scope(lvl)),
			Expr::HOp(_, args, rel, _) => {
				args.iter().all(|arg| arg.in_scope(lvl)) && rel.in_scope(lvl)
			},
		}
	}

	fn exprs(&self) -> Vector<&Expr> {
		match self {
			Expr::Log(l) => l.exprs(),
			Expr::Op(op, es, ty)
				if matches!(
					op.as_str(),
					"=" | "EQ" | "<=" | "LE" | "<" | "LT" | ">=" | "GE" | ">" | "GT"
				) && es.len() == 2 && ty == &DataType::Boolean =>
			{
				es.iter().collect()
			},
			Expr::Op(_, es, _) | Expr::HOp(_, es, _, _) => {
				es.iter().flat_map(Expr::exprs).collect()
			},
			_ => vector![],
		}
	}
}

impl UExpr {
	fn deps(&self, vars: &Range<usize>) -> HashSet<VL> {
		HashSet::unions(self.iter().map(|t| t.deps(vars)))
	}

	fn in_scope(&self, lvl: usize) -> bool {
		self.iter().all(|t| t.in_scope(lvl))
	}

	fn exprs(&self) -> Vector<&Expr> {
		self.iter().flat_map(Term::exprs).collect()
	}
}

impl Relation {
	fn deps(&self, vars: &Range<usize>) -> HashSet<VL> {
		self.1.deps(vars)
	}

	fn in_scope(&self, lvl: usize) -> bool {
		let Lambda(scope, body) = self;
		body.in_scope(lvl + scope.len())
	}

	fn exprs(&self) -> Vector<&Expr> {
		self.1.exprs()
	}
}

impl Term {
	fn deps(&self, vars: &Range<usize>) -> HashSet<VL> {
		let Sigma(_, Inner { logic, apps }) = self;
		logic.deps(vars) + HashSet::unions(apps.iter().map(|app| app.deps(vars)))
	}

	fn in_scope(&self, lvl: usize) -> bool {
		let Sigma(scope, Inner { logic, apps }) = self;
		let lvl = lvl + scope.len();
		logic.in_scope(lvl) && apps.iter().all(|app| app.in_scope(lvl))
	}

	fn exprs(&self) -> Vector<&Expr> {
		let Sigma(_, Inner { logic, apps }) = self;
		logic.exprs() + apps.iter().flat_map(Neutral::exprs).collect()
	}
}

impl Neutral {
	fn deps(&self, vars: &Range<usize>) -> HashSet<VL> {
		let Neut(head, args) = self;
		(match &head {
			Head::Var(_) => HashSet::new(),
			Head::HOp(_, args, rel) => {
				rel.deps(vars) + HashSet::unions(args.iter().map(|arg| arg.deps(vars)))
			},
		}) + HashSet::unions(args.iter().map(|arg| arg.deps(vars)))
	}

	fn in_scope(&self, lvl: usize) -> bool {
		let Neut(head, args) = self;
		(match &head {
			Head::Var(_) => true,
			Head::HOp(_, args, rel) => {
				args.iter().all(|arg| arg.in_scope(lvl)) && rel.in_scope(lvl)
			},
		}) && args.iter().all(|arg| arg.in_scope(lvl))
	}

	fn exprs(&self) -> Vector<&Expr> {
		let Neut(head, args) = self;
		(match &head {
			Head::Var(_) => vector![],
			Head::HOp(_, args, rel) => {
				args.iter().flat_map(Expr::exprs).chain(rel.exprs()).collect()
			},
		}) + args.iter().flat_map(Expr::exprs).collect()
	}
}

impl Logic {
	fn deps(&self, vars: &Range<usize>) -> HashSet<VL> {
		use shared::Logic::*;
		match self {
			Bool(e) => e.deps(vars),
			Eq(e1, e2) => e1.deps(vars) + e2.deps(vars),
			Pred(_, args) => HashSet::unions(args.iter().map(|arg| arg.deps(vars))),
			Neg(l) => l.deps(vars),
			And(ls) | Or(ls) => HashSet::unions(ls.iter().map(|l| l.deps(vars))),
			Squash(u) => u.deps(vars),
		}
	}

	fn in_scope(&self, lvl: usize) -> bool {
		use shared::Logic::*;
		match self {
			Bool(e) => e.in_scope(lvl),
			Eq(e1, e2) => e1.in_scope(lvl) && e2.in_scope(lvl),
			Pred(_, args) => args.iter().all(|arg| arg.in_scope(lvl)),
			Neg(l) => l.in_scope(lvl),
			And(ls) | Or(ls) => ls.iter().all(|l| l.in_scope(lvl)),
			Squash(u) => u.in_scope(lvl),
		}
	}

	fn simpl(self) -> Self {
		use shared::Logic::*;
		match self {
			Eq(e1, e2) if e1 == e2 => Logic::tt(),
			Bool(Expr::Op(p, es, _)) if p == "=" && es.len() == 2 && es[0] == es[1] => {
				!es[0].clone().is_null()
			},
			And(ls) => And(ls
				.into_iter()
				.flat_map(|l| match l.simpl() {
					And(ls) => ls,
					l => vector![l],
				})
				.collect()),
			Or(ls) => Or(ls
				.into_iter()
				.flat_map(|l| match l.simpl() {
					Or(ls) => ls,
					l => vector![l],
				})
				.collect()),
			Neg(l) => Neg(l.simpl().into()),
			l => l,
		}
	}

	pub(crate) fn exprs(&self) -> Vector<&Expr> {
		use shared::Logic::*;
		match self {
			Bool(e) => e.exprs(),
			Pred(_, es) => es.iter().flat_map(Expr::exprs).collect(),
			Eq(e1, e2) => vector![e1, e2] + e1.exprs() + e2.exprs(),
			Neg(l) => l.exprs(),
			And(ls) => ls.iter().flat_map(Logic::exprs).collect(),
			Or(ls) => ls.iter().flat_map(Logic::exprs).collect(),
			Squash(u) => u.exprs(),
		}
	}
}

// pub type Env = Vector<DataType>;
#[derive(Clone)]
pub struct Env {
	types: Vector<DataType>,
	nulls: Vector<bool>,
	catalog: Rc<Vec<Schema>>,
}

impl Env {
	pub fn new(types: Vector<DataType>, catalog: Rc<Vec<Schema>>) -> Self {
		let nulls: Vector<bool> = iter::repeat(true).take(types.len()).collect();
		Self { types, nulls, catalog }
	}

	pub fn new_with_nulls(
		types: Vector<DataType>,
		nulls: Vector<bool>,
		catalog: Rc<Vec<Schema>>,
	) -> Self {
		assert_eq!(types.len(), nulls.len(), "types / nullability mismatch");
		Self { types, nulls, catalog }
	}

	pub fn nulls(&self) -> &Vector<bool> { &self.nulls }

    pub fn extend(&self, scope: &Vector<DataType>) -> Self {
		let more_nulls: Vector<bool> = iter::repeat(true).take(scope.len()).collect();
        Self { 
			types: self.types.clone() + scope.clone(), 
			nulls: self.nulls.clone() + more_nulls,
			catalog: self.catalog.clone() 
		}
    }

	pub fn from_types(types: Vector<DataType>) -> Self {
        // Self { types, catalog: Rc::new(Vec::new()) }
		Self::new(types, Rc::new(Vec::new()))
    }
}

/* impl Deref for Env {
    type Target = Vector<DataType>;
    fn deref(&self) -> &Self::Target { &self.types }
}

impl Add<&Vector<DataType>> for &Env {
    type Output = Env;
    fn add(self, rhs: &Vector<DataType>) -> Env {
        Env { types: self.types.clone() + rhs.clone(), catalog: self.catalog.clone() }
    }
} */
impl Deref for Env {
	type Target = Vector<DataType>;
	fn deref(&self) -> &Self::Target { &self.types }
}

impl Add<&Vector<DataType>> for &Env {
	type Output = Env;
	#[inline]
	fn add(self, rhs: &Vector<DataType>) -> Env { self.extend(rhs) }
}

impl Eval<partial::Aggr, Expr> for &Env {
	fn eval(self, agg: partial::Aggr) -> Expr {
		use shared::Expr::*;
		let op = agg.0.clone();
		let ty = agg.ty();
		let es = Agg(agg).split(&op, self).into_iter().map(|(scp, l, apps, e)| {
			let env = &(self + &scp);
			let inner = Inner { logic: env.eval(l), apps: env.eval(apps) };
			Agg(Aggr(op.clone(), scp, Box::new(inner), Box::new(env.eval(e))))
		});
		Op(op.clone(), es.collect(), ty)
	}
}

impl Eval<partial::UExpr, UExpr> for &Env {
	fn eval(self, source: partial::UExpr) -> UExpr {
		source
			.into_iter()
			.flat_map(|t| t.split(self))
			.map(|(scp, l, apps)| {
				let env = &(self + &scp);
				Sigma(scp, Inner { logic: env.eval(l), apps: env.eval(apps) })
			})
			.collect()
	}
}

impl Eval<(VL, DataType), Expr> for &Env {
	fn eval(self, source: (VL, DataType)) -> Expr {
		Expr::Var(source.0, source.1)
	}
}

impl Eval<partial::Relation, Relation> for &Env {
	fn eval(self, source: partial::Relation) -> Relation {
		let partial::Relation(scope, clos_env, body) = source;
		let env = &(self + &scope);
		let vars = shared::Expr::vars(self.len(), scope.clone());
		let body: partial::UExpr = (&clos_env.append(vars)).eval(body);
		Lambda(scope, env.eval(body))
	}
}

impl<'c> Eval<stable::Relation<'c>, Relation> for &Env {
	fn eval(self, stable::Relation(scope, env, body): stable::Relation<'c>) -> Relation {
		let body = (&env.extend(self.len(), scope.clone())).eval(body);
		Lambda(scope.clone(), (&(self + &scope)).eval(body))
	}
}

impl<'c> Eval<stable::UExpr<'c>, UExpr> for &Env {
	fn eval(self, source: stable::UExpr<'c>) -> UExpr {
		source.into_iter().filter_map(|t| self.eval(t)).collect()
	}
}

impl<'c> Eval<stable::Term<'c>, Option<Term>> for &Env {
	fn eval(self, stable::Term(scope, clos_env, inner): stable::Term<'c>) -> Option<Term> {
		let (new_scope, new_subst) = stablize(&clos_env, scope.clone(), self, inner.logic.clone())?;
		let stable::Env(subst, z3_env) = clos_env;
		let clos_env = &stable::Env(subst + new_subst, z3_env.extend(&scope));
		let env = &(self + &new_scope);
		let logic = env.eval(clos_env.eval(inner.logic));
		let apps = env.eval(clos_env.eval(inner.apps));
		Some(Sigma(new_scope, Inner { logic, apps }))
	}
}

impl<'c> Eval<stable::Aggr<'c>, Expr> for &Env {
	fn eval(self, agg: stable::Aggr<'c>) -> Expr {
		use shared::Expr::*;
		let op = agg.0.clone();
		let ty = agg.ty();
		let es = Agg(agg).split(&op, self).into_iter().map(|(scp, l, apps, e)| {
			let env = &(self + &scp);
			let inner = Inner { logic: env.eval(l), apps: env.eval(apps) };
			Agg(Aggr(op.clone(), scp, Box::new(inner), Box::new(env.eval(e))))
		});
		Op(op.clone(), es.collect(), ty)
	}
}

impl Unify<partial::UExpr> for Env {
	fn unify(&self, t1: &partial::UExpr, t2: &partial::UExpr) -> bool {
		let t1: UExpr = self.eval(t1.clone());
		let t2: UExpr = self.eval(t2.clone());
		let config = Config::new();
		let z3_ctx = Context::new(&config);
		let ctx = Rc::new(Ctx::new(Solver::new(&z3_ctx)));
		let subst = shared::Expr::vars(0, self.types.clone()).into_iter().map(Some).collect();
		let z3_subst: Vector<_> = self.iter().map(|ty| ctx.var(ty, "v")).collect();
		let env = &stable::Env(subst, Z3Env::new(ctx.clone(), z3_subst.clone(), self.catalog.clone()));
		let t1 = env.eval(t1);
		let t2 = env.eval(t2);
		let t1: UExpr = self.eval(t1);
		let t2: UExpr = self.eval(t2);
		let top = Bool::from_bool(ctx.z3_ctx(), true);
		let uni_env = UnifyEnv(ctx, z3_subst.clone(), z3_subst, top);
		uni_env.unify(&t1, &t2)
	}
}

pub type HOpMap<'c> = HashMap<(String, Vec<Expr>, Relation, Vector<Dynamic<'c>>), Dynamic<'c>>;

pub type RelHOpMap<'c> =
	HashMap<(String, Vec<Expr>, Relation, Vector<Dynamic<'c>>, bool), (String, Vec<DataType>)>;

pub type AggMap<'c> =
	HashMap<(String, Lambda<(Inner, Vec<Expr>)>, Vector<Dynamic<'c>>), Dynamic<'c>>;

#[derive(Clone)]
pub struct Z3Env<'c> {
	pub ctx: Rc<Ctx<'c>>,
	pub tuple_sort: Sort<'c>,
	pub subst: Vector<Dynamic<'c>>,
	pub phi: Option<Bool<'c>>, 	// Global Constraints
	pub h_ops: Rc<RefCell<HOpMap<'c>>>,
	pub aggs: Rc<RefCell<AggMap<'c>>>,
	pub rel_h_ops: Rc<RefCell<RelHOpMap<'c>>>,
	pub catalog: Rc<Vec<Schema>>,
}

impl<'c> Z3Env<'c> {
	#[inline]
	fn bool_true(&self) -> Bool<'c> {
		Bool::from_bool(self.ctx.z3_ctx(), true)
	}

	pub fn fresh_tuple_vars_of(&self, schema: &[DataType]) -> Vector<Dynamic<'c>> {
		schema.iter().map(|ty| self.ctx.var(ty, "t")).collect()
	}

	pub fn rel_app(
        &self,
        name: &str,
        args: &[Dynamic<'c>],
        result_ty: &DataType,
        nullable: bool,
    ) -> Dynamic<'c> {
        let arg_refs: Vec<&Dynamic<'c>> = args.iter().collect();
        self.ctx.app(name, &arg_refs, result_ty, nullable)
    }

	pub fn equal_expr(&self, e1: &rel::Expr, e2: &rel::Expr) -> Bool<'c> {
        use rel::Expr::*;

        if let (
            Op { op: op1, args: cols1, ty: _, rel: None },
            Op { op: op2, args: cols2, ty: _, rel: None },
        ) = (e1, e2)
            && op1.eq_ignore_ascii_case("ROW")
            && op2.eq_ignore_ascii_case("ROW")
        {
            if cols1.is_empty() && cols2.is_empty() {
                return Bool::from_bool(self.ctx.z3_ctx(), true);
            }

            if cols1.len() == cols2.len() {
                let col_eqs: Vec<Dynamic<'c>> = cols1
                    .iter()
                    .zip(cols2)
                    .map(|(c1, c2)| {
                        assert_eq!(c1.ty(), c2.ty(), "ROW-equality: column type mismatch");
                        self.equal(c1.ty(), &self.eval(c1), &self.eval(c2))
                    })
                    .collect();

                let all = self.ctx.bool_and_v(&col_eqs.iter().collect::<Vec<_>>());
                return self.ctx.bool_is_true(&all);
            }
        }
        let d1 = self.eval(e1);
        let d2 = self.eval(e2);
        assert_eq!(
            d1.get_sort(),
            d2.get_sort(),
            "Mismatching sorts: {:?} vs {:?}",
            e1,
            e2
        );

        let nullable_eq = self.equal(e1.ty(), &d1, &d2);
        self.ctx.bool_is_true(&nullable_eq)
    }

	pub fn equal_nonnull(
		&self, ty: &DataType, a1: &Dynamic<'c>, a2: &Dynamic<'c>,
	) -> Dynamic<'c> {
		let tri = self.equal(ty.clone(), a1, a2);
		let strict = self.ctx.bool_is_true(&tri);
		self.ctx.bool_some(strict)
	}

	pub fn cmp_nonnull(
        &self,
        ty: DataType,
        cmp: &str,
        a1: &Dynamic<'c>,
        a2: &Dynamic<'c>,
    ) -> Dynamic<'c> {
        let tri = self.cmp(ty.clone(), cmp, a1, a2);
        let strict = self.ctx.bool_is_true(&tri);
        self.ctx.bool_some(strict)
    }

	pub fn encode_subset(&self, t1: &TupCtx<'c>, _r1: &rel::Relation, t2: &TupCtx<'c>, _r2: &rel::Relation) -> Bool<'c> {
		let z3_ctx = self.ctx.z3_ctx();

		// Build one opaque “tuple” object that will stand for a row of either relation.
		// We model membership of a tuple in a relation via the unary predicate
		//   rel!<name>p(tuple) : Bool
		// and then assert    rel₁(t) ⇒ rel₂(t)   for all tuples t.
		//
		// A single uninterpreted sort is sufficient, because attributes are accessed
		// through separate uninterpreted functions that take the same tuple as their
		// first (and only) argument.
		let tuple_sort = z3::Sort::uninterpreted(
			z3_ctx,
			z3::Symbol::String("Tuple".into())
		);
		let t = z3::ast::Dynamic::fresh_const(z3_ctx, "t", &tuple_sort);

		// Helper that builds the unary membership predicate symbol “rel!<name>p”.
		let pred = |name: &str| {
			let f = z3::FuncDecl::new(
				z3_ctx,
				format!("{}p", Self::u_name_of_relation(name)),
				&[&tuple_sort],
				&z3::Sort::bool(z3_ctx),
			);
			f.apply(&[&t]).as_bool().unwrap()
		};

		let in_r1 = pred(&t1.rel_name);
		let in_r2 = pred(&t2.rel_name);

		// ∀t.  in_r1(t)  ⇒  in_r2(t)
		let forall = {
			let bound : [&dyn z3::ast::Ast; 1] = [&t];
			z3::ast::forall_const(z3_ctx, &bound, &[], &in_r1.implies(&in_r2))
		};

		forall
	}

	pub fn encode_subattr(&self, a1: &rel::Expr, a2: &rel::Expr) -> Bool<'c> {
		use z3::ast::{forall_const, exists_const};

        let z3_ctx  = self.ctx.z3_ctx();
        let tuple_s = &self.tuple_sort;

        // bound variables
        let t  = Dynamic::fresh_const(z3_ctx, "t",  &tuple_s);
        let tp = Dynamic::fresh_const(z3_ctx, "t'", &tuple_s);

        // unary “membership” predicates
        let mem  = |name: &str, tup: &Dynamic<'c>| {
            let f = z3::FuncDecl::new(
                z3_ctx,
                format!("{}p", Self::u_name_of_relation(name)),
                &[&tuple_s],
                &z3::Sort::bool(z3_ctx),
            );
            f.apply(&[tup]).as_bool().unwrap()
        };

        // tuple contexts for attribute evaluation
        let tup1 = TupCtx { rel_name: "r1".into(), cols: vector![t.clone()] };
        let tup2 = TupCtx { rel_name: "r2".into(), cols: vector![tp.clone()] };

        let ty   = a1.ty();                       // 공통 타입
        let v1   = self.eval_attr(&tup1, a1);
        let v2   = self.eval_attr(&tup2, a2);

        // ¬null(v1)
        let not_null = {
            let null = self.ctx.none(&ty).unwrap();
            null._eq(&v1).not()
        };

        // a₂(t') = a₁(t)   (Null-세이프 동등 / strict Bool)
        let eq_val  = self.ctx.bool_is_true(&self.equal(ty, &v1, &v2));

        // 본문 : R₂(t') ∧ a₂(t') = a₁(t)
        let body = Bool::and(z3_ctx, &[&mem("r2", &tp), &eq_val]);

        // ∃ t'. body
        let exists  = {
            let bnds : [&dyn Ast; 1] = [&tp];
            exists_const(z3_ctx, &bnds, &[], &body)
        };

        // ∀ t.    ¬null(a₁(t))  ⇒  ∃ …
        let antecedent = not_null;
        let conseq     = exists;
        let implication = antecedent.implies(&conseq);

        let bnds : [&dyn Ast; 1] = [&t];
        forall_const(z3_ctx, &bnds, &[], &implication)
	}

	pub fn eval_attr(&self, tup: &TupCtx<'c>, e: &rel::Expr) -> Dynamic<'c> {
		use rel::Expr::*;
		match e {
			Col { column: VL(i), ty } => tup.attr(self, *i, ty),
			Op { op, args, ty, rel: None } => {
                let dargs: Vec<_> = args.iter().map(|a| self.eval_attr(tup, a)).collect();
                self.ctx.app(&Self::uf_name_of_expr(op), &dargs.iter().collect::<Vec<_>>(), ty, true)
            }
            Op { op, args, ty, rel: Some(q) } => {
                let dargs: Vec<_> = args.iter().map(|a| self.eval(a)).collect();
                self.ctx.app(&Self::uf_name_of_expr(op), &dargs.iter().collect::<Vec<_>>(), ty, true)
            }
		}
	}

	pub fn encode_refattr(
		&self,
		_r1: &rel::Relation,
		a1: &rel::Expr,
		_r2: &rel::Relation,
		a2: &rel::Expr,
	) -> Bool<'c> {
		use z3::ast::{forall_const, exists_const};

        let z3_ctx  = self.ctx.z3_ctx();
        let tuple_s = &self.tuple_sort;

        let t  = Dynamic::fresh_const(z3_ctx, "t",  &tuple_s);
        let tp = Dynamic::fresh_const(z3_ctx, "t'", &tuple_s);

        let mem = |name: &str, tup: &Dynamic<'c>| {
            let f = z3::FuncDecl::new(
                z3_ctx,
                format!("{}p", Self::u_name_of_relation(name)),
                &[&tuple_s],
                &z3::Sort::bool(z3_ctx),
            );
            f.apply(&[tup]).as_bool().unwrap()
        };

        let tup1 = TupCtx { rel_name: "r1".into(), cols: vector![t.clone()] };
        let tup2 = TupCtx { rel_name: "r2".into(), cols: vector![tp.clone()] };

        let ty   = a1.ty();
        let v1   = self.eval_attr(&tup1, a1);
        let v2   = self.eval_attr(&tup2, a2);

        let not_null = {
            let null = self.ctx.none(&ty).unwrap();
            null._eq(&v1).not()
        };

        let eq_val = self.ctx.bool_is_true(&self.equal(ty, &v1, &v2));

        let body   = Bool::and(z3_ctx, &[&mem("r2", &tp), &eq_val]);

        let exists = {
            let bnds : [&dyn Ast; 1] = [&tp];
            exists_const(z3_ctx, &bnds, &[], &body)
        };

        let antecedent = Bool::and(z3_ctx, &[&mem("r1", &t), &not_null]);
        let implication = antecedent.implies(&exists);

        let bnds : [&dyn Ast; 1] = [&t];
        forall_const(z3_ctx, &bnds, &[], &implication)
	}

	pub fn encode_unique(&self, r: &rel::Relation, a: &rel::Expr) -> Bool<'c> {
		use z3::ast::forall_const;

        let z3_ctx  = self.ctx.z3_ctx();
        let tuple_s = &self.tuple_sort;

		let rel_name = Self::u_name_of_relation(&r.name());
        let t  = Dynamic::fresh_const(z3_ctx, "t", &tuple_s);
        let u  = Dynamic::fresh_const(z3_ctx, "u", &tuple_s);

        let mem = |tup: &Dynamic<'c>| {
            let f = z3::FuncDecl::new(
                z3_ctx,
                format!("{}p", rel_name),
                &[&tuple_s],
                &z3::Sort::bool(z3_ctx),
            );
            f.apply(&[tup]).as_bool().unwrap()
        };

        let tup_t = TupCtx { rel_name: rel_name.clone(), cols: vector![t.clone()] };
        let tup_u = TupCtx { rel_name: rel_name.clone(), cols: vector![u.clone()] };

        let ty    = a.ty();
        let vt    = self.eval_attr(&tup_t, a);
        let vu    = self.eval_attr(&tup_u, a);
        let eq_a  = self.ctx.bool_is_true(&self.equal(ty, &vt, &vu));

        let antecedent = Bool::and(z3_ctx, &[&mem(&t), &mem(&u), &eq_a]);
        let implication = antecedent.implies(&t._eq(&u));

        let bnds : [&dyn Ast; 2] = [&t, &u];
        forall_const(z3_ctx, &bnds, &[], &implication)
	}

	pub fn encode_notnull(&self, r: &rel::Relation, a: &rel::Expr) -> Bool<'c> {
		use z3::ast::forall_const;

        let z3_ctx  = self.ctx.z3_ctx();
        let tuple_s = &self.tuple_sort;

        let rel_name = Self::u_name_of_relation(&r.name());

        let mem = |tup: &Dynamic<'c>| {
            let f = z3::FuncDecl::new(
                z3_ctx,
                format!("{}p", rel_name),
                &[&tuple_s],
                &z3::Sort::bool(z3_ctx),
            );
            f.apply(&[tup]).as_bool().unwrap()
        };

		let t = Dynamic::fresh_const(z3_ctx, "t", &tuple_s);
        let tup = TupCtx { rel_name: rel_name.clone(), cols: vector![t.clone()] };

        let ty   = a.ty();
        let val  = self.eval_attr(&tup, a);
        let not_null = {
            let null = self.ctx.none(&ty).unwrap();
            null._eq(&val).not()
        };

        let implication = mem(&t).implies(&not_null);
        let bnds : [&dyn Ast; 1] = [&t];
        forall_const(z3_ctx, &bnds, &[], &implication)
	}

	pub fn encode_fd(
		&self,
		r: &rel::Relation,
		x: &Vec<rel::Expr>,
		y: &Vec<rel::Expr>,
	) -> Bool<'c> {
		use z3::ast::forall_const;

        assert!(!x.is_empty() && !y.is_empty(),
                "FD must have non-empty X and Y");

        let z3_ctx  = self.ctx.z3_ctx();
        let tuple_s = &self.tuple_sort;

		let rel_name = Self::u_name_of_relation(&r.name());
        let t  = Dynamic::fresh_const(z3_ctx, "t", &tuple_s);
        let u  = Dynamic::fresh_const(z3_ctx, "u", &tuple_s);

        let mem = |tup: &Dynamic<'c>| {
            let f = z3::FuncDecl::new(
                z3_ctx,
                format!("{}p", rel_name),
                &[&tuple_s],
                &z3::Sort::bool(z3_ctx),
            );
            f.apply(&[tup]).as_bool().unwrap()
        };

        let tup_t = TupCtx { rel_name: rel_name.clone(), cols: vector![t.clone()] };
        let tup_u = TupCtx { rel_name: rel_name.clone(), cols: vector![u.clone()] };

        let eq_xs : Vec<Bool<'c>> = x.iter().map(|e| {
            let ty  = e.ty();
            let vt  = self.eval_attr(&tup_t, e);
            let vu  = self.eval_attr(&tup_u, e);
            self.ctx.bool_is_true(&self.equal(ty, &vt, &vu))
        }).collect();

        let eq_ys : Vec<Bool<'c>> = y.iter().map(|e| {
            let ty  = e.ty();
            let vt  = self.eval_attr(&tup_t, e);
            let vu  = self.eval_attr(&tup_u, e);
            self.ctx.bool_is_true(&self.equal(ty, &vt, &vu))
        }).collect();

        let antecedent = Bool::and(
			z3_ctx,
			&[&mem(&t), &mem(&u),
			&Bool::and(z3_ctx, &eq_xs.iter().collect::<Vec<_>>())],
		);

        let conseq      = Bool::and(z3_ctx, &eq_ys.iter().collect::<Vec<_>>());
        let implication = antecedent.implies(&conseq);

        let bnds : [&dyn Ast; 2] = [&t, &u];
        forall_const(z3_ctx, &bnds, &[], &implication)
	}

	pub fn encode_const(&self, r: &rel::Relation, a: &rel::Expr, c: &rel::Expr) -> Bool<'c> {
		use z3::ast::forall_const;

        let z3_ctx  = self.ctx.z3_ctx();
        let tuple_s = &self.tuple_sort;

		let rel_name = Self::u_name_of_relation(&r.name());
        let t = Dynamic::fresh_const(z3_ctx, "t", &tuple_s);

        let mem = |tup: &Dynamic<'c>| {
            let f = z3::FuncDecl::new(
                z3_ctx,
                format!("{}p", rel_name),
                &[&tuple_s],
                &z3::Sort::bool(z3_ctx),
            );
            f.apply(&[tup]).as_bool().unwrap()
        };

        let tup = TupCtx { rel_name: rel_name.clone(), cols: vector![t.clone()] };

        let ty      = a.ty();
        let val_t   = self.eval_attr(&tup, a);
        let val_c   = self.eval(c);
        let eq_val  = self.ctx.bool_is_true(&self.equal(ty, &val_t, &val_c));

        let implication = mem(&t).implies(&eq_val);

        let bnds : [&dyn Ast; 1] = [&t];
        forall_const(z3_ctx, &bnds, &[], &implication)
	}

	pub fn empty(ctx: Rc<Ctx<'c>>, catalog: Rc<Vec<Schema>>) -> Self {
		Self::new(ctx, vector![], catalog)
	}

	pub fn new(ctx: Rc<Ctx<'c>>, subst: Vector<Dynamic<'c>>, catalog: Rc<Vec<Schema>>) -> Self {
		let tuple_sort = Sort::uninterpreted(ctx.z3_ctx(), z3::Symbol::String("Tuple".into()));
		Z3Env {
			ctx,
			subst,
			phi: None, // Global constraints
			h_ops: Default::default(),
			aggs: Default::default(),
			rel_h_ops: Default::default(),
			catalog,
			tuple_sort,
		}
	}

	/// Store φ in the environment (to be called once, right after evaluation).
    pub fn set_phi(&mut self, phi: Bool<'c>) { self.phi = Some(phi); }

    /// Push φ into the *current* solver frame (a no-op if φ is `None`).
    pub fn assert_phi(&self) {
        if let Some(ref phi) = self.phi {
            self.ctx.solver.assert(phi);
        }
    } 

	pub fn extend(&self, scope: &Vector<DataType>) -> Self {
		// let vars = scope.into_iter().map(|ty| self.ctx.var(ty, "v")).collect();
		// Z3Env { subst: self.subst.clone() + vars, catalog: self.catalog.clone(), phi: self.phi.clone(), ..self.clone() }

		let mut subst = self.subst.clone();
		for ty in scope {
			subst.push_back(self.ctx.var(ty, "v"));
		}

		Z3Env {
			ctx: self.ctx.clone(),
			tuple_sort: self.tuple_sort.clone(),
			subst,
			phi: self.phi.clone(),
			h_ops: self.h_ops.clone(),
			aggs: self.aggs.clone(),
			rel_h_ops: self.rel_h_ops.clone(),
			catalog: self.catalog.clone(),
		}
	}

	pub fn extend_vals(&self, vals: &Vector<Dynamic<'c>>) -> Self {
		Z3Env { subst: &self.subst + vals, phi: self.phi.clone(), ..self.clone() }
	}

	pub fn extend_vars(&self, scope: &Vector<DataType>) -> (Z3Env<'c>, Vector<Dynamic<'c>>) {
		let vars = scope.into_iter().map(|ty| self.ctx.var(ty, "v")).collect();
		(Z3Env { subst: &self.subst + &vars, phi: self.phi.clone(), ..self.clone() }, vars)
	}

	fn exists(&self, vars: &Vector<Dynamic<'c>>, body: &Bool<'c>) -> Bool<'c> {
		let z3_ctx = self.ctx.z3_ctx();
		let bounds = vars.iter().map(|v| v as &dyn Ast).collect_vec();
		exists_const(z3_ctx, &bounds, &[], body)
	}

	fn equal(&self, ty: DataType, a1: &Dynamic<'c>, a2: &Dynamic<'c>) -> Dynamic<'c> {
		let nonnull_hint = {
			let strict = self.ctx.strict_sort(&ty);
			a1.get_sort() == strict || a2.get_sort() == strict
		};

		use shared::DataType::*;
		let ctx = &self.ctx;
		let strict_sort = ctx.strict_sort(&ty);

		// Helper: lift a strict value into an `Option<…>::Some(_)`
		// so that both operands share the *nullable* sort.
		let strict_sort = ctx.strict_sort(&ty);
		let lift = |v: &Dynamic<'c>| -> Dynamic<'c> {
			if v.get_sort() == strict_sort {
				match ty {
					Integer => {
						// `as_int()` gives the underlying `z3::ast::Int`
						ctx.int_some(v.as_int().expect("Expected Int"))
					}
					Real => ctx.real_some(v.as_real().expect("Expected Real")),
					Boolean => ctx.bool_some(v.as_bool().expect("Expected Bool")),
					String => ctx.string_some(v.as_string().expect("Expected String")),
					// For custom / uninterpreted sorts we keep the value as‑is;
					// equality will fall back to `generic_eq`.
					Custom(_) => v.clone(),
				}
			} else {
				v.clone()
			}
		};

		if nonnull_hint {
			return self.equal_nonnull(&ty, a1, a2);
		}

		let v1 = lift(a1);
		let v2 = lift(a2);

		// At this point both operands must have the same (nullable) sort.
		debug_assert!(
			v1.get_sort() == v2.get_sort(),
			"equal(): sort mismatch after lifting: {:?} vs {:?}",
			v1.get_sort(),
			v2.get_sort()
		);

		match ty {
			Integer => ctx.int__eq(&v1, &v2),
			Real => ctx.real__eq(&v1, &v2),
			Boolean => ctx.bool__eq(&v1, &v2),
			String => ctx.string__eq(&v1, &v2),
			Custom(name) => ctx.generic_eq(name, &v1, &v2),
		}
	}

	fn cmp(&self, ty: DataType, cmp: &str, a1: &Dynamic<'c>, a2: &Dynamic<'c>) -> Dynamic<'c> {
		let nonnull_hint = {
			let strict = self.ctx.strict_sort(&ty);
			a1.get_sort() == strict || a2.get_sort() == strict
		};

		if nonnull_hint {
			return self.cmp_nonnull(ty.clone(), cmp, a1, a2);
		}

		let ctx = &self.ctx;
		use shared::DataType::*;
		assert!(matches!(ty, Integer | Real | String));
		match cmp {
			">" | "GT" => match ty {
				Integer => ctx.int_gt(a1, a2),
				Real => ctx.real_gt(a1, a2),
				_ => ctx.string_gt(a1, a2),
			},
			"<" | "LT" => match ty {
				Integer => ctx.int_lt(a1, a2),
				Real => ctx.real_lt(a1, a2),
				_ => ctx.string_lt(a1, a2),
			},
			">=" | "GE" => match ty {
				Integer => ctx.int_ge(a1, a2),
				Real => ctx.real_ge(a1, a2),
				_ => ctx.string_ge(a1, a2),
			},
			"<=" | "LE" => match ty {
				Integer => ctx.int_le(a1, a2),
				Real => ctx.real_le(a1, a2),
				_ => ctx.string_le(a1, a2),
			},
			_ => unreachable!(),
		}
	}

	#[inline]
	fn u_name_of_relation(relation: &str) -> String {
		format!("rel!{}", relation)
	}

	#[inline]
    fn uf_name_of_expr(op: &str) -> String {
        format!("f!{}", op.replace('\'', "\""))
    }

	fn attr_app(
        &self,
        rel_name: &str,
        attr_idx: usize,
        tuple: &[&Dynamic<'c>],
        ty: &DataType,
		nullable: bool,
    ) -> Dynamic<'c> {
        let uf = format!("{}!c{}", Self::u_name_of_relation(rel_name), attr_idx);
        self.ctx.app(&uf, tuple, ty, nullable)
    }

	// Some x.P
	// exists x. (P[x] == true) => true
	// exists x. (P[x] == null) => null
	// otherwise, forall x. (P[x] == false) => false
	// All x.P
	// exists x. (P[x] == false) => false
	// exists x. (P[x] == null), => null
	// otherwise, forall x. (P[x] == true) => true
	fn quant_cmp(&self, quant: &str, cmp: &str, args: &Vec<Expr>, rel: &Relation) -> Dynamic<'c> {
		let ctx = &self.ctx;
		let z3_ctx = self.ctx.z3_ctx();
		let Lambda(scope, uexpr) = rel.clone();
		assert_eq!(scope.len(), args.len());
		let vals = args.into_iter().map(|a| self.eval(a)).collect_vec();
		let (ref inner_env, vars) = self.extend_vars(&scope);
		let cmp: Dynamic<'c> = match cmp {
			"=" | "EQ" | "<>" | "!=" | "NE" => {
				let cmps = vals
					.iter()
					.zip(&vars)
					.zip(scope)
					.map(|((v, x), ty)| match cmp {
						"=" | "EQ" => self.equal(ty, v, x),
						_ => self.ctx.bool_not(&self.equal(ty, v, x)),
					})
					.collect_vec();
				self.ctx.bool_and_v(&cmps.iter().collect_vec())
			},
			_ if vals.len() == 1 => self.cmp(scope[0].clone(), cmp, &vals[0], &vars[0]),
			_ => todo!(),
		};
		let body = inner_env.eval(&uexpr);
		// r => exists x. v <cmp> x == r /\ |R(x)|
		/* let p = |res| self.exists(&vars, &Bool::and(z3_ctx, &[&cmp._eq(res), &body]));
		match quant {
			"SOME" | "ANY" => p(&ctx.bool(Some(true))).ite(
				&ctx.bool(Some(true)),
				&p(&ctx.bool(None)).ite(&ctx.bool(None), &ctx.bool(Some(false))),
			),
			_ => p(&ctx.bool(Some(false))).ite(
				&ctx.bool(Some(false)),
				&p(&ctx.bool(None)).ite(&ctx.bool(None), &ctx.bool(Some(true))),
			),
		} */
		let any_true = self.exists(&vars, &Bool::and(z3_ctx, &[&cmp._eq(&ctx.bool(Some(true))), &body]));
        let any_false = self.exists(&vars, &Bool::and(z3_ctx, &[&cmp._eq(&ctx.bool(Some(false))), &body]));
        let any_null = self.exists(&vars, &Bool::and(z3_ctx, &[&cmp._eq(&ctx.bool(None)), &body]));
        match quant {
            // ANY / SOME
            "ANY" | "SOME" => any_true.ite(
                &ctx.bool(Some(true)),
                &any_null.ite(&ctx.bool(None), &ctx.bool(Some(false))),
            ),
            // ALL
            "ALL" | _ => any_false.ite(
                &ctx.bool(Some(false)),
                &any_null.ite(&ctx.bool(None), &ctx.bool(Some(true))),
            ),
		}
	}
}

impl<'c> Eval<&Logic, Bool<'c>> for &Z3Env<'c> {
	fn eval(self, source: &Logic) -> Bool<'c> {
		use shared::Logic::*;
		let Z3Env { ctx, .. } = self;
		let z3_ctx = ctx.z3_ctx();
		match source {
			Bool(e) => ctx.bool_is_true(&self.eval(e)),
			Eq(e1, e2) => {
				assert_eq!(e1.ty(), e2.ty(), "{} and {} have different types", e1, e2);
				self.eval(e1)._eq(&self.eval(e2))
			},
			Pred(p, args) => {
				let args = args.iter().map(|arg| self.eval(arg)).collect_vec();
				let args = args.iter().collect_vec();
				ctx.app(p, &args, &DataType::Boolean, false).as_bool().unwrap()
			},
			Neg(l) => self.eval(l.as_ref()).not(),
			And(ls) => z3::ast::Bool::and(z3_ctx, &self.eval(ls).iter().collect_vec()),
			Or(ls) => z3::ast::Bool::or(z3_ctx, &self.eval(ls).iter().collect_vec()),
			Squash(u) => self.eval(u.as_ref()),
		}
	}
}

impl<'c> Eval<&UExpr, Bool<'c>> for &Z3Env<'c> {
	fn eval(self, source: &UExpr) -> Bool<'c> {
		let terms = source.iter().map(|t| self.eval(t)).collect_vec();
		Bool::or(self.ctx.z3_ctx(), &terms.iter().collect_vec())
	}
}

impl<'c> Eval<&Term, Bool<'c>> for &Z3Env<'c> {
	fn eval(self, Sigma(scope, body): &Term) -> Bool<'c> {
		let (ref env, vars) = self.extend_vars(scope);
		self.exists(&vars, &env.eval(body))
	}
}

impl<'c> Eval<&Inner, Bool<'c>> for &Z3Env<'c> {
	fn eval(self, source: &Inner) -> Bool<'c> {
		Bool::and(self.ctx.z3_ctx(), &[&self.eval(&source.logic), &self.eval(&source.apps)])
	}
}

impl<'c> Eval<&Vector<Neutral>, Bool<'c>> for &Z3Env<'c> {
	fn eval(self, source: &Vector<Neutral>) -> Bool<'c> {
		let apps: Vector<_> = self.eval(source);
		let z3_ctx = self.ctx.z3_ctx();
		if apps.is_empty() {
			Bool::from_bool(z3_ctx, true)
		} else {
			Bool::and(z3_ctx, &apps.iter().collect_vec())
		}
	}
}

impl<'c> Eval<&Vector<Neutral>, Int<'c>> for &Z3Env<'c> {
	fn eval(self, source: &Vector<Neutral>) -> Int<'c> {
		let apps: Vector<_> = self.eval(source);
		let z3_ctx = self.ctx.z3_ctx();
		if apps.is_empty() {
			Int::from_i64(z3_ctx, 1)
		} else {
			Int::mul(z3_ctx, &apps.iter().collect_vec())
		}
	}
}

impl<'c> shared::Eval<&rel::Expr, Dynamic<'c>> for &Z3Env<'c> {
	fn eval(self, source: &rel::Expr) -> Dynamic<'c> {
		use rel::Expr::*;
		match source {
			Op { op, args, ty, rel: None } => {
                let dargs: Vec<Dynamic<'c>> =
                    args.iter().map(|a| self.eval(a)).collect();
                let arefs: Vec<&Dynamic<'c>> = dargs.iter().collect();
                self.ctx.app(&Z3Env::uf_name_of_expr(op), &arefs, ty, true)
            }

            Op { op, args, ty, rel: Some(_q) } => {
                let dargs: Vec<Dynamic<'c>> =
                    args.iter().map(|a| self.eval(a)).collect();
                let arefs: Vec<&Dynamic<'c>> = dargs.iter().collect();
                self.ctx.app(&Z3Env::uf_name_of_expr(op), &arefs, ty, true)
            }

			Col { .. } => unreachable!("Col should be lowered via eval_attr()")
		}
	}
}

fn table_name(head: &Head, env: &Z3Env, squashed: bool, domain: Vec<DataType>) -> String {
	let Z3Env { subst, rel_h_ops, .. } = env;
	match head {
		Head::Var(VL(l)) => format!("r{}!{}", if squashed { "p" } else { "" }, l),
		Head::HOp(op, args, rel) => {
			let len = rel_h_ops.borrow().len();
			let name = format!("rh{}!{}", if squashed { "p" } else { "" }, len);
			rel_h_ops
				.borrow_mut()
				.entry((op.clone(), args.clone(), *rel.clone(), subst.clone(), squashed))
				.or_insert((name, domain))
				.0
				.clone()
		},
	}
}

impl<'c> Eval<&Neutral, Bool<'c>> for &Z3Env<'c> {
	fn eval(self, shared::Neutral(head, args): &Neutral) -> Bool<'c> {
		let domain = args.iter().map(|a| a.ty()).collect();
		/* let args = args.iter().map(|v| self.eval(v)).collect_vec();
		let args = args.iter().collect_vec();
		self.ctx
			.app(&(table_name(head, self, true, domain) + "p"), &args, &DataType::Boolean, false)
			.as_bool()
			.unwrap() */
		let dargs: Vec<Dynamic<'c>> = args.iter().map(|v| self.eval(v)).collect();
		self.rel_app(
			&(table_name(head, self, true, domain) + "p"),
			&dargs, 
			&DataType::Boolean, 
			false,
		).as_bool().unwrap()
	}
}

impl<'c> Eval<&Neutral, Int<'c>> for &Z3Env<'c> {
	fn eval(self, shared::Neutral(head, args): &Neutral) -> Int<'c> {
		let domain = args.iter().map(|a| a.ty()).collect();
		let dargs = args.iter().map(|v| self.eval(v)).collect_vec();
		/* let args = args.iter().collect_vec();
		self.ctx
			.app(&table_name(head, self, false, domain), &args, &DataType::Integer, false)
			.as_int()
			.unwrap() */
		self.rel_app(
			&table_name(head, self, false, domain),
			&dargs,
			&DataType::Integer,
			false,
		).as_int().unwrap()
	}
}

impl<'c> Eval<&Expr, Dynamic<'c>> for &Z3Env<'c> {
	fn eval(self, source: &Expr) -> Dynamic<'c> {
		use DataType::*;
		let Z3Env { ctx, subst, h_ops, aggs, .. } = self;
		let parse = |ctx: &Ctx<'c>, input: &str, ty: &DataType| -> anyhow::Result<Dynamic<'c>> {
			if input.to_lowercase() == "null" {
				let null = match ty {
					Integer => ctx.int_none(),
					Real => ctx.real_none(),
					Boolean => ctx.bool_none(),
					String => ctx.string_none(),
					_ => bail!("unsupported type {:?} for null", ty),
				};
				return Ok(null);
			}
			let z3_ctx = ctx.z3_ctx();
			Ok(match ty {
				Integer => ctx.int_some(Int::from_i64(z3_ctx, input.parse()?)),
				Real => {
					let r: f32 = input.parse()?;
					let r = num::rational::Ratio::from_float(r).unwrap();
					ctx.real_some(Re::from_real(
						z3_ctx,
						r.numer().to_i32().unwrap(),
						r.denom().to_i32().unwrap(),
					))
				},
				Boolean => ctx.bool(Some(input.to_lowercase().parse()?)),
				String => ctx.string_some(Str::from_str(z3_ctx, input).unwrap()),
				_ => bail!("unsupported type {:?} for constant {}", ty, input),
			})
		};
		match source {
			Expr::Var(VL(l), _) => subst[*l].clone(),
			Expr::Log(l) => ctx.bool_some(self.eval(l.as_ref())),
			Expr::Op(op, args, ty)
				if args.is_empty()
					&& let Ok(exp) = parse(ctx.as_ref(), op, ty) =>
			{
				exp
			},
			Expr::Op(op, expr_args, ty) => {
				let args = expr_args.iter().map(|a| self.eval(a)).collect_vec();
				let args = args.iter().collect_vec();
				match op.as_str() {
					op if num_op(op) && ty == &Integer => match op {
						"+" | "PLUS" | "UNARY PLUS" => ctx.int_add_v(&args),
						"-" | "MINUS" | "UNARY MINUS" => ctx.int_sub_v(&args),
						"*" | "MULT" => ctx.int_mul_v(&args),
						"/" | "DIV" => ctx.int_div(args[0], args[1]),
						"%" => ctx.int_modulo(args[0], args[1]),
						// "POWER" => ctx.int_power(args[0], args[1]),
						_ => unreachable!(),
					},
					op if num_op(op) && ty == &Real => match op {
						"+" | "PLUS" | "UNARY PLUS" => ctx.real_add_v(&args),
						"-" | "MINUS" | "UNARY MINUS" => ctx.real_sub_v(&args),
						"*" | "MULT" => ctx.real_mul_v(&args),
						"/" | "DIV" => ctx.real_div(args[0], args[1]),
						// "POWER" => ctx.real_power(args[0], args[1]),
						_ => unreachable!(),
					},
					cmp @ (">" | "GT" | "<" | "LT" | ">=" | "GE" | "<=" | "LE")
						if matches!(expr_args[0].ty(), Integer | Real | String) =>
					{
						self.cmp(expr_args[0].ty(), cmp, args[0], args[1])
					},
					"=" | "EQ" => self.equal(expr_args[0].ty(), args[0], args[1]),
					"<>" | "!=" | "NE" => {
						self.ctx.bool_not(&self.equal(expr_args[0].ty(), args[0], args[1]))
					},
					"NOT" if args.len() == 1 => ctx.bool_not(args[0]),
					"AND" => ctx.bool_and_v(&args),
					"OR" => ctx.bool_or_v(&args),
					"CASE" if args.len() % 2 == 1 => {
						let (chunks, remainder) = args.as_chunks();
						chunks.iter().rfold(remainder[0].clone(), |rem, [cond, body]| {
							ctx.bool_is_true(cond).ite(body, &rem)
						})
					},
					"CASE" if args.len() >= 2 && args.len() % 2 == 0 => {
						let input = args[0].clone();
						let (chunks, remainder) = args[1..].as_chunks();
						chunks.iter().rfold(remainder[0].clone(), |rem, [val, body]| {
							input._eq(val).ite(body, &rem)
						})
					},
					"CAST" if ty == &expr_args[0].ty() => args[0].clone(),
					"CAST" if ty == &Real && expr_args[0].ty() == Integer => {
						ctx.int_to_real(args[0])
					},
					"CAST"
						if let Expr::Op(op, args, _) = &expr_args[0]
							&& args.is_empty() && let Ok(exp) = parse(ctx.as_ref(), op, ty) =>
					{
						exp
					},
					"COUNT" | "SUM" | "MIN" | "MAX" => {
						if args.len() == 1 {
							args[0].clone()
						} else {
							ctx.app(&format!("f{}!{}", args.len(), op), &args, ty, true)
						}
					},
					op => ctx.app(&format!("f!{}", op.replace('\'', "\"")), &args, ty, true),
				}
			},
			// TODO: Support inequality between multiple values.
			Expr::HOp(f, args, rel, DataType::Boolean)
				if let Some((cmp, quant)) = f.split_whitespace().collect_tuple()
					&& num_cmp(cmp) && args.len() == 1
					&& matches!(quant, "SOME" | "ANY" | "ALL") =>
			{
				self.quant_cmp(quant, cmp, args, rel)
			},
			Expr::HOp(f, args, rel, DataType::Boolean)
				if let Some((cmp, quant)) = f.split_whitespace().collect_tuple()
					&& matches!(cmp, "=" | "EQ" | "<>" | "!=" | "NE")
					&& matches!(quant, "SOME" | "ANY" | "ALL") =>
			{
				self.quant_cmp(quant, cmp, args, rel)
			},
			Expr::HOp(f, args, rel, DataType::Boolean) if f == "IN" => {
				self.quant_cmp("SOME", "=", args, rel)
			},
			Expr::HOp(f, args, rel, ty) => h_ops
				.borrow_mut()
				.entry((f.clone(), args.clone(), *rel.clone(), subst.clone()))
				.or_insert_with(|| self.ctx.var(ty, "h"))
				.clone(),
			Expr::Agg(agg) => {
				let Aggr(f, scope, inner, expr) = agg;
				aggs.borrow_mut()
					.entry((
						f.clone(),
						Lambda(scope.clone(), (*inner.clone(), vec![*expr.clone()])),
						subst.clone(),
					))
					.or_insert_with(|| self.ctx.var(&expr.ty(), "h"))
					.clone()
			},
		}
	}
}

impl<'c> Eval<&Vec<constraint::Constraint>, Bool<'c>> for &Z3Env<'c> {
	fn eval(self, constraints: &Vec<constraint::Constraint>) -> Bool<'c> {
		use constraint::Constraint::*;
		let z3_ctx = self.ctx.z3_ctx();

		let encoded: Vec<Bool<'c>> = constraints
			.iter()
			.map(|c| match c {
				RelEq { r1, r2 } => {
                    let t1 = TupCtx { rel_name: "r1".to_string(), cols: vector![] };
                    let t2 = TupCtx { rel_name: "r2".to_string(), cols: vector![] };

                    let l2r = self.encode_subset(&t1, r1, &t2, r2);
                    let r2l = self.encode_subset(&t2, r2, &t1, r1);
                    Bool::and(z3_ctx, &[&l2r, &r2l])
                }
				AttrsEq { a1, a2 } => {
					self.equal_expr(a1, a2)
				},
				PredEq { p1, p2 } => {
					self.equal_expr(p1, p2)
				},
				SubAttr { a1, a2 } => {
					self.encode_subattr(a1, a2)
				},
				RefAttr { r1, a1, r2, a2 } => {
					self.encode_refattr(r1, a1, r2, a2)
				},
				Unique { r, a } => {
					self.encode_unique(r, a)
				},
				NotNull { r, a } => {
					self.encode_notnull(r, a)
				},
				FD { r, x, y } => {
					self.encode_fd(r, x, y)
				},
				Const { a, r, c } => {
					self.equal_expr(a, c)
				},
				Subset { r1, r2 } => {
                    let t1 = TupCtx { rel_name: "r1".to_string(), cols: vector![] };
                    let t2 = TupCtx { rel_name: "r2".to_string(), cols: vector![] };
                    self.encode_subset(&t1, r1, &t2, r2)
                }
			})
			.collect();

		if encoded.is_empty() {
			Bool::from_bool(z3_ctx, true)
		} else {
			Bool::and(z3_ctx, &encoded.iter().collect::<Vec<_>>())
		}
	}
}

#[derive(Clone)]
pub struct TupCtx<'c> {
	pub rel_name: String,
	pub cols: Vector<Dynamic<'c>>,
}

impl<'c> TupCtx<'c> {
	#[inline]
	pub fn attr(&self, z3: &Z3Env<'c>, idx: usize, ty: &DataType) -> Dynamic<'c> {
		let mut nullable = true;

		if let Some(body) = self.rel_name.strip_prefix('r') {
			let num: String = body.chars().take_while(|c| c.is_ascii_digit()).collect();
			if let Ok(tid) = num.parse::<usize>() {
				if let Some(schema) = z3.catalog.get(tid) {
					if let Some(&n) = schema.nullabilities.get(idx) {
						nullable = n;
					}
				}
			}
		}

		z3.attr_app(
			&self.rel_name,
			idx,
			&self.cols.iter().collect::<Vec<_>>(),
			ty,
			nullable,
		)
	}
}
