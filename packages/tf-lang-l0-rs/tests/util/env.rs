use std::env;
/// RAII guard for scoped env overrides to prevent test flakiness.
pub struct EnvVarGuard {
    key: String,
    prev: Option<String>,
}
impl EnvVarGuard {
    pub fn set(key: &str, val: &str) -> Self {
        let prev = env::var(key).ok();
        env::set_var(key, val);
        Self { key: key.to_string(), prev }
    }
    pub fn unset(key: &str) -> Self {
        let prev = env::var(key).ok();
        env::remove_var(key);
        Self { key: key.to_string(), prev }
    }
}
impl Drop for EnvVarGuard {
    fn drop(&mut self) {
        match &self.prev {
            Some(v) => env::set_var(&self.key, v),
            None => env::remove_var(&self.key),
        }
    }
}
