use std::sync::atomic::{AtomicU8, Ordering};

/// Centralized, cached environment feature flags for the Rust runtime.
/// 0: uninitialized, 1: false, 2: true
static DEV_PROOFS_STATE: AtomicU8 = AtomicU8::new(0);

pub fn dev_proofs_enabled() -> bool {
    let state = DEV_PROOFS_STATE.load(Ordering::Acquire);
    if state != 0 {
        return state == 2;
    }

    let val = std::env::var("DEV_PROOFS")
        .map(|v| v == "1" || v.eq_ignore_ascii_case("true"))
        .unwrap_or(false);
    let new_state = if val { 2 } else { 1 };

    match DEV_PROOFS_STATE.compare_exchange(0, new_state, Ordering::Release, Ordering::Acquire) {
        Ok(_) => val,
        Err(current_state) => current_state == 2,
    }
}

/// TESTS ONLY: clear cached flags
pub fn __reset_env_cache_for_tests__() {
    DEV_PROOFS_STATE.store(0, Ordering::Release);
}
