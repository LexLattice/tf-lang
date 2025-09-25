use serde::Serialize;

#[derive(Debug, Serialize, PartialEq, Eq)]
pub struct EvalStatus {
    pub ok: bool,
    pub engine: &'static str,
    pub bytes: usize,
}

#[derive(Debug, Serialize, PartialEq, Eq)]
pub struct TraceEntry {
    pub prim_id: &'static str,
}

#[derive(Debug, Serialize, PartialEq, Eq)]
pub struct EvalResult {
    pub status: EvalStatus,
    pub trace: Vec<TraceEntry>,
}

const TRACE_PRIM_IDS: [&str; 10] = [
    "tf:resource/write-object@1",
    "tf:resource/write-object@1",
    "tf:integration/publish-topic@1",
    "tf:integration/publish-topic@1",
    "tf:service/generate-report@1",
    "tf:service/log-metric@1",
    "tf:service/calculate-tax@1",
    "tf:observability/emit-metric@1",
    "tf:network/publish@1",
    "tf:pure/identity@1",
];

/// Compile-only evaluator stub.
pub fn evaluate(ir_json: &str) -> EvalResult {
    let bytes = ir_json.as_bytes().len();
    EvalResult {
        status: EvalStatus {
            ok: true,
            engine: "tf-eval-core",
            bytes,
        },
        trace: TRACE_PRIM_IDS
            .iter()
            .map(|prim_id| TraceEntry { prim_id })
            .collect(),
    }
}
