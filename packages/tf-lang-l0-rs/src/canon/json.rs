use anyhow::{anyhow, Result};
use serde_json::Value;

pub fn canonical_json_bytes(v: &Value) -> Result<Vec<u8>> {
    fn canonical(v: &Value, out: &mut String) -> Result<()> {
        match v {
            Value::Null => out.push_str("null"),
            Value::Bool(b) => out.push_str(if *b { "true" } else { "false" }),
            Value::Number(n) => {
                if let Some(i) = n.as_i64() {
                    out.push_str(&i.to_string());
                } else if let Some(u) = n.as_u64() {
                    out.push_str(&u.to_string());
                } else if n.as_f64().map(|f| f == 0.0).unwrap_or(false) {
                    out.push('0');
                } else {
                    return Err(anyhow!("E_L0_FLOAT"));
                }
            }
            Value::String(s) => {
                out.push_str(&serde_json::to_string(s)?);
            }
            Value::Array(arr) => {
                out.push('[');
                let mut first = true;
                for item in arr {
                    if !first {
                        out.push(',');
                    }
                    canonical(item, out)?;
                    first = false;
                }
                out.push(']');
            }
            Value::Object(map) => {
                out.push('{');
                let mut keys: Vec<_> = map.keys().collect();
                keys.sort();
                let mut first = true;
                for k in keys {
                    if !first {
                        out.push(',');
                    }
                    out.push_str(&serde_json::to_string(k)?);
                    out.push(':');
                    canonical(map.get(k).unwrap(), out)?;
                    first = false;
                }
                out.push('}');
            }
        }
        Ok(())
    }

    let mut s = String::new();
    canonical(v, &mut s)?;
    Ok(s.into_bytes())
}
