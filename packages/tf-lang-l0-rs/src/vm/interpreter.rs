use crate::canon::{blake3_hex, canonical_json_bytes};
use crate::model::bytecode::Instr;
use crate::model::{JournalEntry, Program, World};
use crate::vm::opcode::Host;
use crate::proof::Replace;
#[cfg(feature = "dev_proofs")]
use crate::proof::{ProofTag, Effect, NormalizationTarget, TransportOp};
#[cfg(feature = "dev_proofs")]
use crate::proof::ProofMeta;
#[cfg(feature = "dev_proofs")]
use std::time::{SystemTime, UNIX_EPOCH};
use serde_json::Value;

/// Simple VM running SSA bytecode with JSON values as registers.
pub struct VM<'h> {
    pub host: &'h dyn Host,
}

#[cfg(feature = "dev_proofs")]
fn now_ms() -> u64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|d| d.as_millis() as u64)
        .unwrap_or(0)
}

#[cfg(feature = "dev_proofs")]
fn base_meta() -> ProofMeta<'static> {
    ProofMeta {
        runtime: "rust",
        ts: now_ms(),
        region: None,
        gate: None,
        oracle: None,
        seed: None,
    }
}

#[derive(thiserror::Error, Debug)]
pub enum VmError {
    #[error("register out of bounds: r{0} (regs={1})")]
    RegOutOfBounds(u16, usize),
    #[error("invalid bytecode: {0}")]
    Invalid(String),
}

impl<'h> VM<'h> {
    pub fn run(&self, prog: &Program) -> anyhow::Result<Value> {
        let mut regs: Vec<Value> = vec![serde_json::Value::Null; prog.regs as usize];
        let mut initial_state = regs[0].clone();
        let mut init_captured = false;

        // helper to read a register with explicit lifetime
        fn get<'a>(r: u16, regs: &'a Vec<Value>) -> anyhow::Result<&'a Value> {
            match regs.get(r as usize) {
                Some(v) => Ok(v),
                None => Err(VmError::RegOutOfBounds(r, regs.len()).into()),
            }
        }

        for ins in &prog.instrs {
            match ins {
                Instr::Halt => break,
                Instr::Assert { pred, msg } => {
                    let v = get(*pred, &regs)?;
                    if !v.as_bool().unwrap_or(false) {
                        #[cfg(feature = "dev_proofs")]
                        if crate::proof::dev_proofs_enabled() {
                            let mut meta = base_meta();
                            meta.gate = Some("assert".into());
                            crate::emit_tag!(
                                ProofTag::Refutation { code: "ASSERT".into(), msg: Some(msg.clone()) },
                                meta
                            );
                        }
                        return Err(VmError::Invalid(format!("ASSERT failed: {}", msg)).into());
                    }
                }
                Instr::Const { dst, value } => {
                    regs[*dst as usize] = value.clone();
                }
                Instr::Pack {
                    dst,
                    tag,
                    regs: rgs,
                } => {
                    let mut arr = Vec::with_capacity(rgs.len());
                    for r in rgs {
                        arr.push(get(*r, &regs)?.clone());
                    }
                    let obj = serde_json::json!({ "tag": tag, "values": arr });
                    regs[*dst as usize] = obj;
                }
                Instr::Unpack { dsts, tag, src } => {
                    let v = get(*src, &regs)?;
                    let o = v
                        .as_object()
                        .ok_or_else(|| VmError::Invalid("UNPACK expects object".into()))?;
                    let found_tag = o
                        .get("tag")
                        .and_then(|t| t.as_str())
                        .ok_or_else(|| VmError::Invalid("UNPACK missing tag".into()))?;
                    if found_tag != tag {
                        return Err(VmError::Invalid(format!(
                            "UNPACK tag mismatch: expected {}, got {}",
                            tag, found_tag
                        ))
                        .into());
                    }
                    let values = o
                        .get("values")
                        .and_then(|v| v.as_array())
                        .ok_or_else(|| VmError::Invalid("UNPACK missing values".into()))?
                        .clone();
                    if values.len() != dsts.len() {
                        return Err(VmError::Invalid("UNPACK arity mismatch".into()).into());
                    }
                    for (i, d) in dsts.iter().enumerate() {
                        regs[*d as usize] = values[i].clone();
                    }
                }
                Instr::IdHash { dst, src } => {
                    let bytes = canonical_json_bytes(get(*src, &regs)?)?;
                    regs[*dst as usize] = serde_json::json!(blake3_hex(&bytes));
                }
                Instr::SnapMake { dst, state } => {
                    let snap = self.host.snapshot_make(get(*state, &regs)?)?;
                    regs[*dst as usize] = snap;
                }
                Instr::SnapId { dst, snapshot } => {
                    let id = self.host.snapshot_id(get(*snapshot, &regs)?)?;
                    regs[*dst as usize] = serde_json::json!(id);
                }
                Instr::LensProj { dst, state, region } => {
                    let sub = self.host.lens_project(get(*state, &regs)?, region)?;
                    #[cfg(feature = "dev_proofs")]
                    if crate::proof::dev_proofs_enabled() {
                        let mut meta = base_meta();
                        meta.region = Some(region.clone());
                        meta.gate = Some("lens_project".into());
                        crate::emit_tag!(
                            ProofTag::Transport { op: TransportOp::LensProj, region: region.clone() },
                            meta
                        );
                    }
                    regs[*dst as usize] = sub;
                }
                Instr::LensMerge {
                    dst,
                    state,
                    region,
                    sub,
                } => {
                    let merged = self
                        .host
                        .lens_merge(get(*state, &regs)?, region, get(*sub, &regs)?)?;
                    #[cfg(feature = "dev_proofs")]
                    if crate::proof::dev_proofs_enabled() {
                        let mut meta = base_meta();
                        meta.region = Some(region.clone());
                        meta.gate = Some("lens_merge".into());
                        crate::emit_tag!(
                            ProofTag::Transport { op: TransportOp::LensMerge, region: region.clone() },
                            meta
                        );
                    }
                    regs[*dst as usize] = merged;
                }
                Instr::PlanSim {
                    dst_delta,
                    dst_world,
                    world,
                    plan,
                } => {
                    // A placeholder: encode the pair (Δ, W') via a TF call
                    let res = self.host.call_tf(
                        "tf://plan/simulate@0.1",
                        &[get(*world, &regs)?.clone(), get(*plan, &regs)?.clone()],
                    )?;
                    let obj = res.as_object().ok_or_else(|| {
                        VmError::Invalid("PlanSim expects object {delta, world}".into())
                    })?;
                    regs[*dst_delta as usize] =
                        obj.get("delta").cloned().unwrap_or(serde_json::Value::Null);
                    regs[*dst_world as usize] =
                        obj.get("world").cloned().unwrap_or(serde_json::Value::Null);
                }
                Instr::DiffApply { dst, state, delta } => {
                    let out = self
                        .host
                        .diff_apply(get(*state, &regs)?, get(*delta, &regs)?)?;
                    regs[*dst as usize] = out;
                }
                Instr::DiffInvert { dst, delta } => {
                    let inv = self.host.diff_invert(get(*delta, &regs)?)?;
                    regs[*dst as usize] = inv;
                }
                Instr::JournalRec {
                    dst,
                    plan,
                    delta,
                    snap0,
                    snap1,
                    meta,
                } => {
                    let s0 = get(*snap0, &regs)?
                        .as_str()
                        .ok_or_else(|| VmError::Invalid("snap0 not string".into()))?;
                    let s1 = get(*snap1, &regs)?
                        .as_str()
                        .ok_or_else(|| VmError::Invalid("snap1 not string".into()))?;
                    let j = self.host.journal_record(
                        get(*plan, &regs)?,
                        get(*delta, &regs)?,
                        s0,
                        s1,
                        get(*meta, &regs)?,
                    )?;
                    regs[*dst as usize] = j.0;
                }
                Instr::JournalRew { dst, world, entry } => {
                    let w = World(get(*world, &regs)?.clone());
                    let j = JournalEntry(get(*entry, &regs)?.clone());
                    let wprev = self.host.journal_rewind(&w, &j)?;
                    regs[*dst as usize] = wprev.0;
                }
                Instr::Call { dst, tf_id, args } => {
                    let mut a = Vec::with_capacity(args.len());
                    for r in args {
                        a.push(get(*r, &regs)?.clone());
                    }
                    let out = self.host.call_tf(tf_id, &a).map_err(|e| {
                        #[cfg(feature = "dev_proofs")]
                        if crate::proof::dev_proofs_enabled() {
                            let mut meta = base_meta();
                            meta.gate = Some("call_tf".into());
                            meta.oracle = Some(tf_id.clone());
                            crate::emit_tag!(
                                ProofTag::Conservativity {
                                    callee: tf_id.clone(),
                                    expected: "ok".into(),
                                    found: format!("{}", e)
                                },
                                meta
                            );
                        }
                        e
                    })?;
                    regs[*dst as usize] = out;
                }
            }
            if !init_captured && regs[0] != serde_json::Value::Null {
                initial_state = regs[0].clone();
                init_captured = true;
            }
        }

        let final_state = regs.get(0).cloned().unwrap_or(serde_json::Value::Null);
        let delta = if final_state == initial_state {
            None
        } else {
            Some(Replace { replace: final_state.clone() })
        };
        #[cfg(feature = "dev_proofs")]
        if crate::proof::dev_proofs_enabled() {
            let mut witness_meta = base_meta();
            witness_meta.gate = Some("vm.run".into());
            crate::emit_tag!(
                ProofTag::Witness { delta: delta.clone(), effect: Effect::default() },
                witness_meta
            );
            for target in [NormalizationTarget::Delta, NormalizationTarget::Effect] {
                let mut meta = base_meta();
                meta.gate = Some("vm.run".into());
                crate::emit_tag!(ProofTag::Normalization { target }, meta);
            }
        }
        let out = match delta {
            None => serde_json::Value::Null,
            Some(d) => serde_json::json!({ "replace": d.replace }),
        };

        Ok(out)
    }
}
