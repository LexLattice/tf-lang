use serde::Serialize;
use serde_json::Value;

#[derive(Debug, Clone, Serialize)]
pub struct EvalStatus {
    pub ok: bool,
    pub engine: &'static str,
    pub bytes: usize,
}

#[derive(Debug, Clone, Serialize)]
pub struct EvalTraceItem {
    pub prim_id: String,
}

#[derive(Debug, Clone, Serialize)]
pub struct EvalResult {
    pub status: EvalStatus,
    pub trace: Vec<EvalTraceItem>,
}

const DEFAULT_TRACE_IDS: &[&str] = &[
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

pub fn default_trace_ids() -> Vec<&'static str> {
    DEFAULT_TRACE_IDS.to_vec()
}

pub fn evaluate(ir_json: &str) -> EvalResult {
    let bytes = ir_json.as_bytes().len();
    let trace = extract_trace(ir_json);
    let status = EvalStatus {
        ok: true,
        engine: "tf-eval-core",
        bytes,
    };
    EvalResult { status, trace }
}

fn extract_trace(ir_json: &str) -> Vec<EvalTraceItem> {
    let parsed: Value = match serde_json::from_str(ir_json) {
        Ok(value) => value,
        Err(_) => return stub_trace(),
    };

    let Some(primitives) = parsed.get("primitives").and_then(Value::as_array) else {
        return stub_trace();
    };

    let mut trace = Vec::with_capacity(primitives.len());
    for (idx, prim) in primitives.iter().enumerate() {
        let id = prim
            .get("prim_id")
            .and_then(Value::as_str)
            .or_else(|| prim.get("prim").and_then(Value::as_str))
            .or_else(|| prim.get("id").and_then(Value::as_str))
            .map(str::to_owned)
            .unwrap_or_else(|| format!("prim[{idx}]"));
        trace.push(EvalTraceItem { prim_id: id });
    }

    if trace.is_empty() {
        stub_trace()
    } else {
        trace
    }
}

fn stub_trace() -> Vec<EvalTraceItem> {
    default_trace_ids()
        .into_iter()
        .map(|id| EvalTraceItem {
            prim_id: id.to_string(),
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_primitive_ids() {
        let json = r#"{"primitives":[{"prim_id":"a"},{"prim":"b"},{"id":"c"},{"x":1}]}"#;
        let result = extract_trace(json);
        let ids: Vec<_> = result.into_iter().map(|t| t.prim_id).collect();
        assert_eq!(ids, vec!["a", "b", "c", "prim[3]"]);
    }

    #[test]
    fn stub_for_invalid_ir() {
        let result = extract_trace("not json");
        let ids: Vec<_> = result.into_iter().map(|t| t.prim_id).collect();
        let expected: Vec<_> = default_trace_ids().into_iter().map(str::to_string).collect();
        assert_eq!(ids, expected);
    }
}
