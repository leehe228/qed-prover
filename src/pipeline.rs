use std::rc::Rc;
use std::time::{Duration, Instant};

use imbl::vector;
use serde::{Deserialize, Serialize};
use z3::{Config, Context, Solver};

use crate::pipeline::normal::Z3Env;
use crate::pipeline::normal::Env as NormEnv;
use crate::pipeline::shared::{Ctx, Eval, Schema};
use crate::pipeline::shared::VL;
use crate::pipeline::relation as rel;
use crate::pipeline::unify::{Unify, UnifyEnv};

pub mod normal;
mod null;
pub mod partial;
pub mod relation;
pub mod shared;
pub mod stable;
pub mod syntax;
#[cfg(test)]
mod tests;
pub mod unify;
pub mod constraint;

#[derive(Serialize, Deserialize)]
pub struct Input {
	schemas: Vec<Schema>,
	pub queries: (relation::Relation, relation::Relation),
	#[serde(default)]
	help: (String, String),
	#[serde(default)]
	pub constraints: Vec<constraint::Constraint>,
}

#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct Stats {
	pub provable: bool,
	pub panicked: bool,
	pub complete_fragment: bool,
	pub equiv_class_duration: Duration,
	pub equiv_class_timed_out: bool,
	pub smt_duration: Duration,
	pub smt_timed_out: bool,
	pub nontrivial_perms: bool,
	pub translate_duration: Duration,
	pub normal_duration: Duration,
	pub stable_duration: Duration,
	pub unify_duration: Duration,
	pub total_duration: Duration,
}

pub fn unify(Input { schemas, queries: (rel1, rel2), help , constraints }: Input) -> (bool, Stats) {
	// ──────────────────────────────────────────────────────────────
	// T1: 제약 기반 스키마 정제 패스 (고정점)
	//
	// ① NotNull, RefAttr, FD(Y)  → 해당 칼럼 nullable = false
	// ② RelEq, Subset            → 릴레이션 간 nullable 전파
	//     고정점에 도달할 때까지 반복
	// ──────────────────────────────────────────────────────────────
	/* let mut schemas = schemas;
	for c in &constraints {
		if let constraint::Constraint::NotNull { r, a } = c {
            if let &rel::Relation::Scan(VL(s_idx)) = r {
				if let Some(schema) = schemas.get_mut(s_idx) {
					// a : &Expr  역시 동일하게 &-패턴 사용
					if let &rel::Expr::Col { column: VL(col_idx), .. } = a {
						if let Some(flag) = schema.nullabilities.get_mut(col_idx) {
							*flag = false;
						}
					}
				}
			}
        }
	} */
	let mut schemas = schemas;
	let mut changed = true;
	let schema_len = schemas.len();

	// Helper: Relation → Option<usize>
	let rel_index = |r: &rel::Relation| -> Option<usize> {
		if let rel::Relation::Scan(VL(idx)) = r { Some(*idx) } else { None }
	};

	// Helper: Expr → Option<usize>   (단순 컬럼일 때만)
	let col_index = |e: &rel::Expr| -> Option<usize> {
		if let rel::Expr::Col { column: VL(idx), .. } = e { Some(*idx) } else { None }
	};

	while changed {
		changed = false;

		for c in &constraints {
			use constraint::Constraint::*;

			match c {
				// 1) 단일 칼럼을 바로 non-null 로 만드는 제약
				NotNull { r, a }
				| RefAttr { r2: r, a2: a, .. } => {
					if let (Some(r_idx), Some(a_idx)) = (rel_index(r), col_index(a)) {
						if let Some(flag) = schemas[r_idx].nullabilities.get_mut(a_idx) {
							if *flag {
								*flag = false;
								changed = true;
							}
						}
					}
				}

				// 2) 기능 종속 FD :   X → Y   ⇒   Y NOT NULL
				FD { r, y, .. } if !y.is_empty() => {
					if let Some(r_idx) = rel_index(r) {
						for e in y {
							if let Some(a_idx) = col_index(e) {
								if let Some(flag) = schemas[r_idx].nullabilities.get_mut(a_idx) {
									if *flag {
										*flag = false;
										changed = true;
									}
								}
							}
						}
					}
				}

				// 3) 릴레이션 간 전파
				RelEq { r1, r2 } | Subset { r1, r2 } => {
					if let (Some(i1), Some(i2)) = (rel_index(r1), rel_index(r2)) {
						let (s1, s2) = {
							// Rust borrow rules: split immutable then mutable
							let (head, tail) = schemas.split_at_mut(i2.max(i1));
							if i1 < i2 {
								(&mut head[i1], &mut tail[0])
							} else if i2 < i1 {
								(&mut tail[0], &mut head[i2])
							} else {
								continue; // 동일 인덱스
							}
						};

						let len = s1.nullabilities.len().min(s2.nullabilities.len());

						for k in 0..len {
							// RelEq : 양방향, Subset : r2(상위) → r1(하위)
							let n1 = s1.nullabilities[k];
							let n2 = s2.nullabilities[k];

							// r2 칼럼이 non-null 이면 r1 도 non-null
							if !n2 && n1 {
								s1.nullabilities[k] = false;
								changed = true;
							}
							// RelEq 이면 반대 방향도
							if matches!(c, RelEq { .. }) && !n1 && n2 {
								s2.nullabilities[k] = false;
								changed = true;
							}
						}
					}
				}

				// 4) 그 외 제약은 nullability에 영향 없음
				AttrsEq { .. } | PredEq { .. } | SubAttr { .. } | Unique { .. } | Const { .. } | FD { .. } => { 
					/* no-op */ 
				}
			}
		}
	}
	
	let mut stats = Stats::default();
	let subst = vector![];
	let env = relation::Env(&schemas, &subst, 0);
	log::info!("Schemas:\n{:?}", schemas);
	log::info!("Input:\n{}\n{}", help.0, help.1);
	stats.complete_fragment = rel1.complete() && rel2.complete();
	if rel1 == rel2 {
		println!("Trivially true!");
		return (true, stats);
	}
	let syn_start = Instant::now();
	log::debug!("Syntax translation started");
	let rel1 = env.eval(rel1);
	let rel2 = env.eval(rel2);
	stats.translate_duration = syn_start.elapsed();
	log::info!("Syntax left:\n{}", rel1);
	log::info!("Syntax right:\n{}", rel2);

	log::debug!("Syntax translation finished - {:.4?}", stats.translate_duration);
	log::trace!("Syntax <- {}\nSyntax -> {}", rel1, rel2);

	if rel1 == rel2 {
		log::debug!("Early exit: equivalent after syntax translation");
		return (true, stats);
	}
	let catalog_rc = Rc::new(schemas.clone());
	// let nom_env = &vector![];
	let nom_env = NormEnv::new(vector![], catalog_rc.clone());
	let eval_nom = |rel: syntax::Relation| -> normal::Relation {
		let rel = (&partial::Env::default()).eval(rel);
		// nom_env.eval(rel)
		(&nom_env).eval(rel)
	};
	let norm_start = Instant::now();
	log::debug!("Normal translation started");
	let rel1 = eval_nom(rel1);
	let rel2 = eval_nom(rel2);
	stats.normal_duration = norm_start.elapsed();
	log::info!("Normal left:\n{}", rel1);
	log::info!("Normal right:\n{}", rel2);
	log::debug!("Normalization finished - {:.4?}", stats.normal_duration);
	log::trace!("Normal <- {}\nNormal -> {}", rel1, rel2);
	if rel1 == rel2 {
		return (true, stats);
	}
	let config = Config::new();
	let z3_ctx = &Context::new(&config);
	let ctx = Rc::new(Ctx::new_with_stats(Solver::new(z3_ctx), stats));
	let mut z3_env = Z3Env::empty(ctx.clone(), catalog_rc.clone());
	let phi = (&z3_env).eval(&constraints);
	z3_env.set_phi(phi.clone()); // Set the constraints in the Z3 environment
	let eval_stb = |nom: normal::Relation| -> normal::Relation {
		let env = &stable::Env(vector![], z3_env.clone());
		let stb = env.eval(nom);
		// nom_env.eval(stb)
		(&nom_env).eval(stb)
	};
	let stb_start = Instant::now();
	log::debug!("Stable translation started");
	let rel1 = eval_stb(rel1);
	let rel2 = eval_stb(rel2);
	ctx.stats.borrow_mut().stable_duration = stb_start.elapsed();
	log::info!("Stable left:\n{}", rel1);
	log::info!("Stable right:\n{}", rel2);
	log::debug!("Stable translation finished - {:.4?}", ctx.stats.borrow().stable_duration);
	log::trace!("Stable <- {}\nStable -> {}", rel1, rel2);
	if rel1 == rel2 {
		return (true, ctx.stats.borrow().clone());
	}
	let phi = (&z3_env).eval(&constraints);
	let env = UnifyEnv(ctx.clone(), vector![], vector![], phi);
	let unify_start = Instant::now();
	log::debug!("Unification started");
	let res = env.unify(&rel1, &rel2);
	ctx.stats.borrow_mut().unify_duration = unify_start.elapsed();
	let stats = ctx.stats.borrow().clone();
	log::debug!("Unification finished - {:.4?}", ctx.stats.borrow().unify_duration);
	log::trace!("Unify <- {}\nUnify -> {}", rel1, rel2);
	(res, stats)
}
