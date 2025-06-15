use serde::{Deserialize, Serialize};
use crate::pipeline::relation as rel;

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "camelCase")]
pub enum Constraint {
    RelEq { r1: rel::Relation, r2: rel::Relation },
    AttrsEq { a1: rel::Expr, a2: rel::Expr },
    PredEq { p1: rel::Expr, p2: rel::Expr },
    SubAttr { a1: rel::Expr, a2: rel::Expr },
    RefAttr {
        r1: rel::Relation, a1: rel::Expr,
        r2: rel::Relation, a2: rel::Expr
    },
    Unique { r: rel::Relation, a: rel::Expr },
    NotNull { r: rel::Relation, a: rel::Expr },
    #[serde(alias = "fd", alias = "FD")]
    FD      { r: rel::Relation, x: Vec<rel::Expr>, y: Vec<rel::Expr> },
    Const   { r: rel::Relation, a: rel::Expr, c: rel::Expr },
    Subset  { r1: rel::Relation, r2: rel::Relation },
}