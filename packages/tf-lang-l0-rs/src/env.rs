use std::sync::OnceLock;
/// Centralized, cached environment feature flags for the Rust runtime.
static mut DEV_PROOFS: OnceLock<bool> = OnceLock::new();

pub fn dev_proofs_enabled() -> bool {
    unsafe {
        *DEV_PROOFS.get_or_init(|| {
            std::env::var("DEV_PROOFS")
                .map(|v| v == "1" || v.eq_ignore_ascii_case("true"))
                .unwrap_or(false)
        })
    }
}

/// TESTS ONLY: clear cached flags
pub fn __reset_env_cache_for_tests__() {
    unsafe {
        DEV_PROOFS.take();
    }
}
