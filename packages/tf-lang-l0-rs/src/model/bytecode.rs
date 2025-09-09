
use serde::{Deserialize, Serialize};

/// SSA-style program; regs are numbered 0..regs-1
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Program {
    pub version: String,
    pub regs: u16,
    pub instrs: Vec<Instr>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(tag = "op", rename_all = "SCREAMING_SNAKE_CASE")]
pub enum Instr {
    Assert { pred: u16, msg: String },
    Halt,
    Const { dst: u16, value: serde_json::Value },
    Pack  { dst: u16, tag: String, regs: Vec<u16> },
    Unpack{ dsts: Vec<u16>, tag: String, src: u16 },

    IdHash { dst: u16, src: u16 },
    SnapMake { dst: u16, state: u16 },
    SnapId { dst: u16, snapshot: u16 },

    LensProj { dst: u16, state: u16, region: String },
    LensMerge{ dst: u16, state: u16, region: String, sub: u16 },

    PlanSim { dst_delta: u16, dst_world: u16, world: u16, plan: u16 },
    DiffApply { dst: u16, state: u16, delta: u16 },
    DiffInvert{ dst: u16, delta: u16 },

    JournalRec { dst: u16, plan: u16, delta: u16, snap0: u16, snap1: u16, meta: u16 },
    JournalRew { dst: u16, world: u16, entry: u16 },

    Call { dst: u16, tf_id: String, args: Vec<u16> },
}
