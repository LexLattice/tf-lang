mod canonical;
mod context;
mod diff;
mod oracle;
mod result;

pub use canonical::{canonical_string, canonicalize, canonicalize_value, CanonError};
pub use context::OracleCtx;
pub use diff::{diff_values, escape_pointer_segment, pointer_from_segments, DiffResult};
pub use oracle::Oracle;
pub use result::{
    err, err_with_details, ok, with_trace, OracleError, OracleFailure, OracleResult, OracleSuccess,
};
