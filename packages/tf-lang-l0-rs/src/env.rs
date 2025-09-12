use std::sync::{Mutex, OnceLock};
/// Centralized, cached environment feature flags for the Rust runtime.
static DEV_PROOFS: OnceLock<Mutex<Option<bool>>> = OnceLock::new();

pub fn dev_proofs_enabled() -> bool {
    let lock = DEV_PROOFS.get_or_init(|| Mutex::new(None));
    let mut cache = lock.lock().unwrap();
    if let Some(v) = *cache {
        v
    } else {
        let v = std::env::var("DEV_PROOFS")
            .map(|v| v == "1" || v.eq_ignore_ascii_case("true"))
            .unwrap_or(false);
        *cache = Some(v);
        v
    }
}

/// TESTS ONLY: clear cached flags
#[doc(hidden)]
pub fn __reset_env_cache_for_tests__() {
    if let Some(lock) = DEV_PROOFS.get() {
        *lock.lock().unwrap() = None;
    }
}
