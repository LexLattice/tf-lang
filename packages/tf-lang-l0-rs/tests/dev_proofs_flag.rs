use tflang_l0::env::{dev_proofs_enabled, __reset_env_cache_for_tests__};
mod util;
use util::env::EnvVarGuard;

#[test]
fn dev_proofs_is_cached() {
    let _g = EnvVarGuard::set("DEV_PROOFS", "1");
    assert!(dev_proofs_enabled());
    drop(_g); // restore
    // Flip env, but cache should hold until reset
    let _g2 = EnvVarGuard::unset("DEV_PROOFS");
    assert!(dev_proofs_enabled());
    __reset_env_cache_for_tests__();
}
