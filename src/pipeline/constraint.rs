use serde::{Deserialize, Serialize};
use crate::pipeline::relation as rel; 
use crate::pipeline::shared::DataType;

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "camelCase")]
pub enum Constraint {
    // c1. Relation Equality - RelEq(r1, r2)
    RelEq { r1: rel::Relation, r2: rel::Relation },

    // c2. Attribute Equality - AttrEq(a1, a2)
    AttrsEq { a1: rel::Expr, a2: rel::Expr },

    // c3. Predicate Equality - PredEq(p1, p2)
    PredEq { p1: rel::Expr, p2: rel::Expr },

    // c4. Sub-Attribute Composition - SubAttr(a1, a2)
    SubAttr { a1: rel::Expr, a2: rel::Expr },

    // c5. Referential Attributes - RefAttr(r1, a1, r2, a2)
    RefAttr {
        r1: rel::Relation, a1: rel::Expr,
        r2: rel::Relation, a2: rel::Expr,
    },

    // c6. Uniqueness - Unique(r, a)
    Unique { r: rel::RefAttr, a: rel::Expr },

    // c7. Non-Null Constraint - NotNull(r, a)
    NotNull { r: rel::RefAttr, a: rel::Expr },

    // c8. Functional Dependence - FD(r, X, Y)
    FD { r: rel::Relation, x: Vec<rel::Expr>, y: Vec<rel::Expr> },

    // c9. Constant - Const(r, a, c)
    Const { r: rel::Relation, a: rel::Expr, c: rel::Expr },

    // c10. Subset - Subset(r1, r2)
    Subset { r1: rel::Relation, r2: rel::Relation },
}
