use std::env;
use std::fs::{create_dir_all, File};
use std::io::Write;
use std::path::Path;
use std::time::{Duration, Instant};
#[cfg(feature = "dev_proofs")]
use std::time::{SystemTime, UNIX_EPOCH};

use serde_json::json;
#[cfg(feature = "dev_proofs")]
use tflang_l0::proof::{flush, ProofMeta, ProofTag, TransportOp};
#[cfg(feature = "dev_proofs")]
use tflang_l0::emit_tag;

const DEFAULT_ITER: u64 = 10_000;
const DEFAULT_RUNS: u64 = 7;

#[cfg(feature = "dev_proofs")]
fn now_ms() -> u64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|d| d.as_millis() as u64)
        .unwrap_or(0)
}

fn run_workload(iterations: u64) {
    #[cfg(feature = "dev_proofs")]
    {
        if !tf_lang_l0::proof::dev_proofs_enabled() {
            return;
        }
        for i in 0..iterations {
            let meta = ProofMeta {
                runtime: "rust",
                ts: now_ms(),
                region: Some("/bench".into()),
                gate: Some("bench.workload".into()),
                oracle: Some("bench".into()),
                seed: Some(i.to_string()),
            };
            emit_tag!(
                ProofTag::Transport {
                    op: TransportOp::LensProj,
                    region: "/bench".into(),
                },
                meta
            );
        }
        let _ = flush();
    }
    #[cfg(not(feature = "dev_proofs"))]
    let _ = iterations;
}

fn main() -> anyhow::Result<()> {
    let iterations: u64 = env::var("ITER")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(DEFAULT_ITER);
    let runs: u64 = env::var("RUNS")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(DEFAULT_RUNS);

    let mut samples = Vec::with_capacity(runs as usize);
    for _ in 0..runs {
        let start = Instant::now();
        run_workload(iterations);
        samples.push(start.elapsed());
    }

    let mean = samples
        .iter()
        .map(Duration::as_secs_f64)
        .sum::<f64>()
        / samples.len() as f64;
    let variance = samples
        .iter()
        .map(Duration::as_secs_f64)
        .map(|s| (s - mean).powi(2))
        .sum::<f64>()
        / samples.len() as f64;
    let stdev = variance.sqrt();

    let mode = if env::var("DEV_PROOFS").ok().as_deref() == Some("1") {
        "on"
    } else {
        "off"
    };

    let samples_ms: Vec<f64> = samples
        .iter()
        .map(|d| d.as_secs_f64() * 1000.0)
        .collect();

    let output = json!({
        "mode": mode,
        "iter": iterations,
        "runs": runs,
        "samples": samples_ms,
        "mean": mean * 1000.0,
        "stdev": stdev * 1000.0,
    });

    let out_dir = Path::new("out/t3/perf");
    create_dir_all(out_dir)?;
    let path = out_dir.join(format!("rs_dev_proofs_{}.json", mode));
    let mut file = File::create(&path)?;
    writeln!(file, "{}", serde_json::to_string_pretty(&output)?)?;
    println!("{}", output.to_string());
    Ok(())
}
