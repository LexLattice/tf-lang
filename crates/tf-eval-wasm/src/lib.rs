use wasm_bindgen::prelude::*;

#[wasm_bindgen]
pub fn run(ir_json: &str) -> Result<JsValue, JsValue> {
    let result = tf_eval_core::evaluate(ir_json);
    serde_wasm_bindgen::to_value(&result).map_err(|err| JsValue::from_str(&err.to_string()))
}
