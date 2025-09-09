
use crate::model::{Effects, Program};

/// Very small placeholder “checker” — expand with SSA/type/effect rules.
pub struct CheckReport {
    pub ok: bool,
    pub observed: Effects,
    pub declared: Effects,
    pub messages: Vec<String>,
}

impl CheckReport {
    pub fn ok(&self) -> bool { self.ok }
}

pub fn type_and_effect_check(_prog: &Program, declared: &Effects) -> CheckReport {
    // TODO: implement SSA, type inference, exhaustiveness, and real effect accounting.
    CheckReport {
        ok: true,
        observed: declared.clone(),
        declared: declared.clone(),
        messages: vec!["checker stub: always ok".into()],
    }
}
