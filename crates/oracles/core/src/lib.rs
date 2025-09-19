mod canonical;
mod context;
mod diff;
mod oracle;
mod result;

pub use canonical::{canonical_string, canonicalize, canonicalize_value, CanonError};
pub use context::OracleCtx;
pub use diff::{
    diff_canonical, escape_pointer_segment, pointer_from_segments, DiffEntry, PointerSegment,
    MISSING_VALUE,
};
pub use oracle::Oracle;
pub use result::{
    err, err_with_details, ok, with_trace, OracleError, OracleFailure, OracleResult, OracleSuccess,
};
