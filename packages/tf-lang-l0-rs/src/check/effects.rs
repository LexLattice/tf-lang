
use crate::model::{Effects, Region};

pub fn allowlist(reads: &[&str], writes: &[&str]) -> Effects {
    let mut e = Effects::default();
    for r in reads { e.add_read(Region((*r).to_string())); }
    for w in writes { e.add_write(Region((*w).to_string())); }
    e
}
