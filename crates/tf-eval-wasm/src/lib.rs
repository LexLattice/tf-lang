use wasm_bindgen::prelude::*;

#[wasm_bindgen]
pub fn run(ir_json: &str) -> Result<JsValue, JsValue> {
    let result = tf_eval_core::evaluate(ir_json);
    serde_wasm_bindgen::to_value(&result).map_err(|err| JsValue::from_str(&err.to_string()))
}

#[wasm_bindgen]
pub fn default_trace_ids() -> js_sys::Array {
    let ids = tf_eval_core::default_trace_ids();
    let array = js_sys::Array::new();
    for id in ids {
        array.push(&JsValue::from_str(id));
    }
    array
}
