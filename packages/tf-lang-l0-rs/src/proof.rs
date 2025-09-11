use crate::model::{Effects, Value};
use serde::{Serialize, Deserialize};

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum ProofTag {
    Witness { delta: Value, effect: Effects },
    Normalization { target: NormalizationTarget },
    Transport { op: TransportOp, region: String },
    Refutation { code: String, msg: Option<String> },
    Conservativity { callee: String, expected: String, found: String },
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum NormalizationTarget {
    Delta,
    Effect,
    State,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum TransportOp {
    LensProj,
    LensMerge,
}
