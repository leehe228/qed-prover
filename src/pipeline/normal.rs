use std::cell::RefCell;
use std::collections::HashMap;
use std::fmt::{Display, Formatter, Write};
use std::ops::{Range, Add, Deref};
use std::rc::Rc;
// use std::iter::{self, FromIterator, Repeat};
use std::iter;

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

	/* fn simpl(self) -> Self {
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
	} */

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
	/* pub fn new(types: Vector<DataType>, catalog: Rc<Vec<Schema>>) -> Self {
		let nulls: Vector<bool> = iter::repeat(true).take(types.len()).collect();
		Self { types, nulls, catalog }
	} */
	pub fn new(types: Vector<DataType>, nulls: Vector<bool>, catalog: Rc<Vec<Schema>>) -> Self {
		assert_eq!(types.len(), nulls.len(), "types / nullability mismatch");
		Self { types, nulls, catalog }
	}

	/* pub fn new_with_nulls(
		types: Vector<DataType>,
		nulls: Vector<bool>,
		catalog: Rc<Vec<Schema>>,
	) -> Self {
		assert_eq!(types.len(), nulls.len(), "types / nullability mismatch");
		Self { types, nulls, catalog }
	} */
	// Convenience constructor that assumes *all* variables are nullable (legacy code‑path).
    pub fn new_all_nullable(types: Vector<DataType>, catalog: Rc<Vec<Schema>>) -> Self {
        let nulls: Vector<bool> = iter::repeat(true).take(types.len()).collect();
        Self { types, nulls, catalog }
    }

	pub fn nulls(&self) -> &Vector<bool> { &self.nulls }

    /* pub fn extend(&self, scope: &Vector<DataType>) -> Self {
		let more_nulls: Vector<bool> = iter::repeat(true).take(scope.len()).collect();
        Self { 
			types: self.types.clone() + scope.clone(), 
			nulls: self.nulls.clone() + more_nulls,
			catalog: self.catalog.clone() 
		}
    } */
	// Extend the environment with a new *scope* and its corresponding nullability vector (T2.2).
    pub fn extend(&self, scope: &Vector<DataType>, nulls_for_scope: &Vector<bool>) -> Self {
        assert_eq!(scope.len(), nulls_for_scope.len(), "scope / nullability mismatch");
        Self {
            types:   self.types.clone() + scope.clone(),
            nulls:   self.nulls.clone() + nulls_for_scope.clone(),
            catalog: self.catalog.clone(),
        }
	}

	/* pub fn from_types(types: Vector<DataType>) -> Self {
        // Self { types, catalog: Rc::new(Vec::new()) }
		Self::new(types, Rc::new(Vec::new()))
    } */
    // Build an empty environment from only the type vector (all nullable).
    pub fn from_types(types: Vector<DataType>) -> Self {
        Self::new_all_nullable(types, Rc::new(Vec::new()))
    }

    // Legacy helper – extend by variables (all nullable).  Existing call‑sites keep working.
    pub fn extend_vars(&self, scope: &Vector<DataType>) -> Self {
        let nulls: Vector<bool> = iter::repeat(true).take(scope.len()).collect();
        self.extend(scope, &nulls)
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

/* impl Deref for Env {
	type Target = Vector<DataType>;
	fn deref(&self) -> &Self::Target { &self.types }
}

impl Add<&Vector<DataType>> for &Env {
	type Output = Env;
	#[inline]
	fn add(self, rhs: &Vector<DataType>) -> Env { self.extend(rhs) }
} */

// T2.3 – keep `Deref` as‑is but update `Add` to propagate nullability
impl Deref for Env {
    type Target = Vector<DataType>;
    fn deref(&self) -> &Self::Target { &self.types }
}

impl Add<&Vector<DataType>> for &Env {
    type Output = Env;
    #[inline]
    fn add(self, rhs: &Vector<DataType>) -> Env {
        // Newly bound variables are assumed *nullable* by default
        let nulls: Vector<bool> = iter::repeat(true).take(rhs.len()).collect();
        self.extend(rhs, &nulls)
    }
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
	/* fn bool_true(&self) -> Bool<'c> {
		Bool::from_bool(self.ctx.z3_ctx(), true)
	} */

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

        let nullable_eq = self.equal_with_hint(e1.ty(), &d1, &d2, true); // apply hint
        self.ctx.bool_is_true(&nullable_eq)
    }

	fn equal_nonnull(
		&self, ty: &DataType, a1: &Dynamic<'c>, a2: &Dynamic<'c>,
	) -> Dynamic<'c> {
		use shared::DataType::*;
		let ctx = &self.ctx;
		let strict_sort = ctx.strict_sort(ty);

		// strict 값이면 Option<…>::Some(_) 로 래핑
		let lift = |v: &Dynamic<'c>| -> Dynamic<'c> {
			if v.get_sort() == strict_sort {
				match ty {
					Integer => ctx.int_some(v.as_int().unwrap()),
					Real    => ctx.real_some(v.as_real().unwrap()),
					Boolean => ctx.bool_some(v.as_bool().unwrap()),
					String  => ctx.string_some(v.as_string().unwrap()),
					Custom(_) => v.clone(),
				}
			} else { v.clone() }
		};
		let v1 = lift(a1);
		let v2 = lift(a2);

		// 이제 두 피연산자는 모두 nullable sort → equal()이 재귀하지 않는다
		let tri = self.equal(ty.clone(), &v1, &v2);
		let strict = ctx.bool_is_true(&tri);
		ctx.bool_some(strict)
	}

	pub fn cmp_nonnull(
        &self,
        ty: DataType,
        cmp: &str,
        a1: &Dynamic<'c>,
        a2: &Dynamic<'c>,
    ) -> Dynamic<'c> {
        use shared::DataType::*;
        let ctx = &self.ctx;
        let strict_sort = ctx.strict_sort(&ty);

        let lift = |v: &Dynamic<'c>| -> Dynamic<'c> {
            if v.get_sort() == strict_sort {
                match ty {
                    Integer => ctx.int_some(v.as_int().unwrap()),
                    Real    => ctx.real_some(v.as_real().unwrap()),
                    String  => ctx.string_some(v.as_string().unwrap()),
                    Boolean => ctx.bool_some(v.as_bool().unwrap()),
                    Custom(_) => v.clone(),
                }
            } else { v.clone() }
        };
        let v1 = lift(a1);
        let v2 = lift(a2);

        let tri = self.cmp(ty.clone(), cmp, &v1, &v2);
        let strict = ctx.bool_is_true(&tri);
        ctx.bool_some(strict)
    }

	pub fn encode_subset(&self, r1: &rel::Relation, r2: &rel::Relation) -> Bool<'c> {
		let z3_ctx   = self.ctx.z3_ctx();
		let tuple_s  = &self.tuple_sort;

		// ① 단일 tuple 상수를 만들고
		let t   = Dynamic::fresh_const(z3_ctx, "t", tuple_s);

		// ② 멤버십 UF 이름은 rel!<tbl>p 형식으로 통일
		let pred = |name: &str| {
			let f = z3::FuncDecl::new(
				z3_ctx,
				format!("{}p", Z3Env::u_name_of_relation(name)),
				&[tuple_s],
				&z3::Sort::bool(z3_ctx),
			);
			f.apply(&[&t]).as_bool().unwrap()
		};

		let in_r1 = pred(&r1.name());
		let in_r2 = pred(&r2.name());

		let bound : [&dyn Ast; 1] = [&t];
		let body  = in_r1.implies(&in_r2);
		z3::ast::forall_const(z3_ctx, &bound, &[], &body)
	}

	pub fn encode_subattr(&self, a1: &rel::Expr, a2: &rel::Expr) -> Bool<'c> {
		use z3::ast::{forall_const, Ast};

		let z3_ctx  = self.ctx.z3_ctx();
		let tuple_s = &self.tuple_sort;

		// 단일 튜플 변수 t : Tuple
		let t = Dynamic::fresh_const(z3_ctx, "t", tuple_s);
		let tup = TupCtx {
			rel_name: "_".into(),          // 실제 릴레이션 이름과 무관
			cols: vector![t.clone()],
		};

		let ty  = a1.ty();                 // a₁, a₂ 공통 타입
		let v1  = self.eval_attr(&tup, a1);    // a₁(t)
		let v2  = self.eval_attr(&tup, a2);    // a₂(t)

		// ¬IsNull(a₁(t))
		let null     = self.ctx.none(&ty).unwrap();
		let is_null  = self.ctx.bool_is_true(&self.equal_with_hint(ty.clone(), &v1, &null, true));
		let not_null = is_null.not();

		// a₁(t) = a₂(t)  (NULL-세이프 비교)
		let eq_val = self.ctx.bool_is_true(&self.equal_with_hint(ty, &v1, &v2, true));

		// ∀t. ¬null(a₁(t)) ⇒ (a₁(t)=a₂(t))
		let impl_ = not_null.implies(&eq_val);
		let bnds : [&dyn Ast; 1] = [&t];
		forall_const(z3_ctx, &bnds, &[], &impl_)
	}

	pub fn eval_attr(&self, tup: &TupCtx<'c>, e: &rel::Expr) -> Dynamic<'c> {
		use rel::Expr::*;
		match e {
			Col { column: VL(i), ty } => tup.attr(self, *i, ty),
			Op { op, args, ty, rel: None } => {
                let dargs: Vec<_> = args.iter().map(|a| self.eval_attr(tup, a)).collect();
                self.ctx.app(&Self::uf_name_of_expr(op), &dargs.iter().collect::<Vec<_>>(), ty, true)
            }
            Op { op, args, ty, rel: Some(_q) } => {
                let dargs: Vec<_> = args.iter().map(|a| self.eval(a)).collect();
                self.ctx.app(&Self::uf_name_of_expr(op), &dargs.iter().collect::<Vec<_>>(), ty, true)
            }
		}
	}

	pub fn encode_refattr(&self, r1: &rel::Relation, a1: &rel::Expr, r2: &rel::Relation, a2: &rel::Expr) -> Bool<'c> {
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

        let tup1 = TupCtx {
			rel_name: Z3Env::u_name_of_relation(&r1.name()),
			cols: vector![t.clone()],
		};
		let tup2 = TupCtx {
			rel_name: Z3Env::u_name_of_relation(&r2.name()),
			cols: vector![tp.clone()],
		};

        let ty   = a1.ty();
        let v1   = self.eval_attr(&tup1, a1);
        let v2   = self.eval_attr(&tup2, a2);

        let not_null = {
			let null = self.ctx.none(&ty).unwrap();
            let is_nil = self.ctx.bool_is_true(&self.equal_with_hint(ty.clone(), &null, &v1, true));
            is_nil.not()
        };

        // let eq_val = self.ctx.bool_is_true(&self.equal(ty, &v1, &v2));
		let eq_val = self.ctx.bool_is_true(&self.equal_with_hint(ty, &v1, &v2, true));

        let body = {
			let r2_name = r2.name();
			Bool::and(z3_ctx, &[&mem(&r2_name, &tp), &eq_val])
		};

        let exists = {
            let bnds : [&dyn Ast; 1] = [&tp];
            exists_const(z3_ctx, &bnds, &[], &body)
        };

        let antecedent = {
			let r1_name = r1.name();
			Bool::and(z3_ctx, &[&mem(&r1_name, &t), &not_null])
		};
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
        let eq_a  = self.ctx.bool_is_true(&self.equal_with_hint(ty, &vt, &vu, true)); // apply hint

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
			let is_nil = self.ctx.bool_is_true(&self.equal_with_hint(ty.clone(), &null, &val, true));
			is_nil.not()
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
            self.ctx.bool_is_true(&self.equal_with_hint(ty, &vt, &vu, true)) // apply hint
        }).collect();

        let eq_ys : Vec<Bool<'c>> = y.iter().map(|e| {
            let ty  = e.ty();
            let vt  = self.eval_attr(&tup_t, e);
            let vu  = self.eval_attr(&tup_u, e);
            self.ctx.bool_is_true(&self.equal_with_hint(ty, &vt, &vu, true)) // apply hint
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
        let eq_val  = self.ctx.bool_is_true(&self.equal_with_hint(ty, &val_t, &val_c, true));

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

	fn equal_inner(&self, ty: DataType, a1: &Dynamic<'c>, a2: &Dynamic<'c>, nonnull_hint: bool) -> Dynamic<'c> {
		use shared::DataType::*;
		let ctx = &self.ctx;
		let strict_sort = ctx.strict_sort(&ty);
		let lift = |v: &Dynamic<'c>| -> Dynamic<'c> {
			if v.get_sort() == strict_sort {
				match ty {
					Integer => ctx.int_some(v.as_int().unwrap()),
					Real => ctx.real_some(v.as_real().unwrap()),
					String => ctx.string_some(v.as_string().unwrap()),
					Boolean => ctx.bool_some(v.as_bool().unwrap()),
					Custom(_) => v.clone(),
				}
			} else { v.clone() }
		};

		let v1 = lift(a1);
		let v2 = lift(a2);

		if nonnull_hint {
			return self.equal_nonnull(&ty, &v1, &v2);
		}

		match ty {
			Integer => ctx.int__eq(&v1, &v2),
			Real => ctx.real__eq(&v1, &v2),
			Boolean => ctx.bool__eq(&v1, &v2),
			String => ctx.string__eq(&v1, &v2),
			Custom(name) => ctx.generic_eq(name, &v1, &v2),
		}
	}

	fn cmp_inner(&self, ty: DataType, cmp: &str, a1: &Dynamic<'c>, a2: &Dynamic<'c>, nonnull_hint: bool) -> Dynamic<'c> {
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

	fn equal(&self, ty: DataType, a1: &Dynamic<'c>, a2: &Dynamic<'c>) -> Dynamic<'c> {
		let auto_hint = {
			let strict = self.ctx.strict_sort(&ty);
			a1.get_sort() == strict || a2.get_sort() == strict
		};
		self.equal_inner(ty, a1, a2, auto_hint)
	}

	pub fn equal_with_hint(&self, ty: DataType, a1: &Dynamic<'c>, a2: &Dynamic<'c>, nonnull_hint: bool) -> Dynamic<'c> {
		self.equal_inner(ty, a1, a2, nonnull_hint)
	}

	fn cmp(&self, ty: DataType, cmp: &str, a1: &Dynamic<'c>, a2: &Dynamic<'c>) -> Dynamic<'c> {
		let auto_hint = {
			let strict = self.ctx.strict_sort(&ty);
			a1.get_sort() == strict || a2.get_sort() == strict
		};
		self.cmp_inner(ty, cmp, a1, a2, auto_hint)
	}

	pub fn cmp_with_hint(&self, ty: DataType, cmp: &str, a1: &Dynamic<'c>, a2: &Dynamic<'c>, nonnull_hint: bool) -> Dynamic<'c> {
		self.cmp_inner(ty, cmp, a1, a2, nonnull_hint)
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

			Col { column: VL(idx), ty } => {
				let sym = format!("col{}", idx);
				self.rel_app(&sym, &[], ty, true)
			}
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
                    let l2r = self.encode_subset(r1, r2);
					let r2l = self.encode_subset(r2, r1);
					Bool::and(z3_ctx, &[&l2r, &r2l])
                }
				AttrsEq { a1, a2 } => {
					let d1 = self.eval(a1);
					let d2 = self.eval(a2);
					let eq = self.equal_with_hint(a1.ty(), &d1, &d2, true);
					self.ctx.bool_is_true(&eq)
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
      				self.encode_subset(r1, r2)
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
		// ──────────────────────────────────────────────────────────────
		// T3 ― Nullable 판정
		//
		// ①  rel_name = "r42" | "r42p"  →  카탈로그 인덱스 42
		// ②  그렇지 않으면 스키마 이름(DDL 상 table 이름)으로 탐색
		// ③  찾은 스키마의 nullabilities[idx] 가 true/false 를 그대로 사용
		//     (T1 패스 이후 이 벡터는 제약을 모두 반영한 최종 결과)
		// ④  매칭 실패 시 보수적으로 `true` 로 간주
		// ──────────────────────────────────────────────────────────────
		let nullable = {
			// 숫자형 식별자( r<n> | r< n >p ) 케이스
			if let Some(num_str) = self
				.rel_name
				.strip_prefix('r')
				.map(|s| s.trim_end_matches('p'))
			{
				if let Ok(tid) = num_str.parse::<usize>() {
					if let Some(schema) = z3.catalog.get(tid) {
						if let Some(&flag) = schema.nullabilities.get(idx) {
							return z3.attr_app(
								&self.rel_name,
								idx,
								&self.cols.iter().collect::<Vec<_>>(),
								ty,
								flag,
							);
						}
					}
				}
			}
			// 이름 매칭 케이스 - 스키마에 `name` 필드가 있다면 직접 비교
			// 이름 기반 매칭 지원 X
			/* if let Some(schema) = z3.catalog.iter().find(|s| s.name == self.rel_name) {
				if let Some(&flag) = schema.nullabilities.get(idx) {
					return z3.attr_app(
						&self.rel_name,
						idx,
						&self.cols.iter().collect::<Vec<_>>(),
						ty,
						flag,
					);
				}
			} */
			// 미확정 → nullable 로 가정
			true
		};

		z3.attr_app(
			&self.rel_name,
			idx,
			&self.cols.iter().collect::<Vec<_>>(),
			ty,
			nullable,
		)
	}
}
