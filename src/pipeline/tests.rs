//! 회귀 테스트 모음 (T7)
//!  - T7.1  example1_const.json      → provable
//!  - T7.2  RefAttr 기반 NOT-NULL    → provable
//!  - T7.3  Subset + FD 고정점 검증  → provable
//!
//! 테스트들은 “provable” 여부만을 단언한다.  
//! 제약 기반 nullability 고정점(T1)이 잘못 구현되면
//! 중간 단계(SMT 모델 생성)가 실패해 provable 결과를 얻지 못하므로
//! 회귀를 충분히 잡아낸다.

#![cfg(test)]

use std::collections::HashMap;

use imbl::vector;
use super::*;
use super::relation as rel;
use super::constraint::Constraint;
use super::shared::{DataType, VL};

/// 경로 헬퍼 – `CARGO_MANIFEST_DIR` 기준 상대 경로를 include
macro_rules! include_json {
    ($path:literal) => {
        include_str!(concat!(env!("CARGO_MANIFEST_DIR"), "/", $path))
    };
}

/// ▲  공통 유틸 ─────────────────────────────────────────────────────────
fn scan(tid: usize) -> rel::Relation {
    rel::Relation::Scan(VL(tid))
}

fn col(idx: usize, ty: DataType) -> rel::Expr {
    rel::Expr::Col { column: VL(idx), ty }
}

fn empty_schema(types: Vec<DataType>, nulls: Vec<bool>) -> Schema {
    Schema {
        types,
        primary: vec![],
        foreign: HashMap::new(),
        nullabilities: nulls,
        guaranteed: vec![],
    }
}

/// ▲  테스트 케이스들 ──────────────────────────────────────────────────
#[test]
fn not_null_example_json_is_provable() {
    // T7.1  – 실제 JSON 파일(example1_const.json)이 이미 repo 내에 존재
    let json = include_json!("examples/7_notnull_c.json");
    let input: super::Input =
        serde_json::from_str(json).expect("examples/7_notnull_c.json must parse");

    let (provable, _stats) = super::unify(input);
    assert!(provable, "examples/7_notnull_c.json should be provable");
}

#[test]
fn refattr_derived_not_null_is_provable() {
    // T7.2  – RefAttr 제약이 nullable=false 로 전파되는지 검사
    let schemas = vec![
        empty_schema(vec![DataType::Integer], vec![true]),  // r0
        empty_schema(vec![DataType::Integer], vec![true]),  // r1
    ];

    let r0 = scan(0);
    let r1 = scan(1);
    let a0 = col(0, DataType::Integer);

    let constraints = vec![
        Constraint::RefAttr {
            r1: r0.clone(),
            a1: a0.clone(),
            r2: r1.clone(),
            a2: a0.clone(),
        },
    ];

    // 쿼리는 동일 - 빈 릴레이션으로 설정 → provable 예상
    let input = super::Input {
        schemas,
        queries: (rel::Relation::Singleton, rel::Relation::Singleton),
        help: Default::default(),
        constraints,
    };

    let (provable, _stats) = super::unify(input);
    assert!(provable, "RefAttr-based NOT-NULL propagation must keep equivalence provable");
}

#[test]
fn fd_and_subset_fixed_point_is_provable() {
    // T7.3  – Subset + FD 조합으로 고정점 반복이 필요한 상황
    let schemas = vec![
        // r0 (하위 집합) : 2 컬럼 모두 nullable = true
        empty_schema(
            vec![DataType::Integer, DataType::Integer],
            vec![true, true],
        ),
        // r1 (상위 집합) : 첫 번째 컬럼만 nonnull, 두 번째는 nullable = true
        empty_schema(
            vec![DataType::Integer, DataType::Integer],
            vec![false, true],
        ),
    ];

    let r0 = scan(0);
    let r1 = scan(1);
    let x   = col(0, DataType::Integer);
    let y   = col(1, DataType::Integer);

    let constraints = vec![
        // r0 ⊆ r1  →  r1 의 non-null 속성이 r0 로 전파 (고정점 필요)
        Constraint::Subset { r1: r0.clone(), r2: r1.clone() },
        // r1 :  X → Y   →  Y 는 non-null (또 다른 전파 요구)
        Constraint::FD { r: r1.clone(), x: vec![x.clone()], y: vec![y.clone()] },
    ];

    let input = super::Input {
        schemas,
        queries: (rel::Relation::Singleton, rel::Relation::Singleton),
        help: Default::default(),
        constraints,
    };

    let (provable, _stats) = super::unify(input);
    assert!(provable, "FD + Subset fixed-point should still prove equivalence");
}
