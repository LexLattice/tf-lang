use tf_eval_core::evaluate;
use wasm_bindgen::prelude::*;

#[wasm_bindgen]
pub fn run(ir_json: &str) -> JsValue {
    let result = evaluate(ir_json);
    serde_wasm_bindgen::to_value(&result).expect("serialize eval result")
}
