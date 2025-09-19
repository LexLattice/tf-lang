#[cfg(feature = "dev_proofs")]
use tflang_l0::proof::{ProofMeta, ProofTag, TransportOp};
#[cfg(feature = "dev_proofs")]
use tflang_l0::emit_tag;
#[cfg(feature = "dev_proofs")]
use std::time::{SystemTime, UNIX_EPOCH};

#[cfg(feature = "dev_proofs")]
fn now_ms() -> u64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|d| d.as_millis() as u64)
        .unwrap_or(0)
}

#[cfg(feature = "dev_proofs")]
fn run() {
    for i in 0..10 {
        let meta = ProofMeta {
            runtime: "rust",
            ts: now_ms(),
            region: Some(format!("/acct/{}", i)),
            gate: Some("trace-smoke".into()),
            oracle: Some("Transport".into()),
            seed: Some(i.to_string()),
        };
        emit_tag!(
            ProofTag::Transport {
                op: TransportOp::LensProj,
                region: format!("/acct/{}", i),
            },
            meta
        );
    }
}

fn main() {
    #[cfg(feature = "dev_proofs")]
    run();
    #[cfg(not(feature = "dev_proofs"))]
    {
        eprintln!("trace-smoke example requires the dev_proofs feature");
    }
}
