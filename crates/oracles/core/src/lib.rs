mod canonical;
mod context;
mod oracle;
mod result;

pub use canonical::{
    canonical_json, canonicalize, canonicalize_from, deep_equal, pointer_from_segments,
    segments_from_pointer, CanonicalizeError, PointerSeg,
};
pub use canonical::pretty_canonical_json;
pub use context::OracleCtx;
pub use oracle::Oracle;
pub use result::{
    err, err_with_details, ok, with_trace, OracleError, OracleFailure, OracleResult, OracleSuccess,
};
