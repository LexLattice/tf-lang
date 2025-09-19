#[macro_export]
macro_rules! emit_tag {
    ($tag:expr, $meta:expr) => {{
        #[cfg(feature = "dev_proofs")]
        {
            $crate::proof::emit_tag(&$tag, &$meta);
        }
    }};
}
