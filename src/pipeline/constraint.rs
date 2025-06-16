use serde::{Deserialize, Serialize};
use crate::pipeline::relation as rel;

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "camelCase")]
pub enum Constraint {
    #[serde(alias = "releq", alias = "RELEQ")]
    RelEq { r1: rel::Relation, r2: rel::Relation },
    #[serde(alias = "attrseq", alias = "ATTRSEQ")]
    AttrsEq { a1: rel::Expr, a2: rel::Expr },
    #[serde(alias = "predeq", alias = "PREDEQ")]
    PredEq { p1: rel::Expr, p2: rel::Expr },
    #[serde(alias = "subattr", alias = "SUBATTR")]
    SubAttr { a1: rel::Expr, a2: rel::Expr },
    #[serde(alias = "refattr", alias = "REFATTR")]
    RefAttr {
        r1: rel::Relation, a1: rel::Expr,
        r2: rel::Relation, a2: rel::Expr
    },
    #[serde(alias = "unique", alias = "UNIQUE")]
    Unique { r: rel::Relation, a: rel::Expr },
    #[serde(alias = "notnull", alias = "NOTNULL")]
    NotNull { r: rel::Relation, a: rel::Expr },
    #[serde(alias = "fd", alias = "FD")]
    FD { r: rel::Relation, x: Vec<rel::Expr>, y: Vec<rel::Expr> },
    #[serde(alias = "const", alias = "CONST")]
    Const { r: rel::Relation, a: rel::Expr, c: rel::Expr },
    #[serde(alias = "subset", alias = "SUBSET")]
    Subset { r1: rel::Relation, r2: rel::Relation },
}
