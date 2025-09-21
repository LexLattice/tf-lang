# L0 DSL Cheatsheet (generated)

## Basics
* `a |> b` composes primitives into a left-associated sequence.
* `seq{ ... }` groups steps explicitly; semicolons separate statements inside the block.
* `par{ ... }` evaluates children in parallel; separate branches with semicolons.
* Bare identifiers call primitives; add `(key=value, ...)` to supply arguments.

## Args & Literals
* Strings accept single or double quotes with standard escape handling.
* Numbers support optional leading `-` and fractional parts.
* Boolean and null literals map to `true`, `false`, and `null`.
* Arrays allow trailing commas and can nest arbitrary literal forms.
* Objects accept string, identifier, or numeric keys with trailing commas.

## Regions
* `authorize{ ... }` fences steps that require explicit capabilities.
* Add attributes with `authorize(scope="kms.sign"){ ... }`; attributes are parsed as key/value pairs.
* `txn{ ... }` introduces a transactional region with the same attribute syntax.
* Region blocks behave like sequence blocks for canonicalization boundaries.

## Comments
* The current tokenizer does not recognize `#` or `//` comments; keep `.tf` files comment-free.

## CLI usage
* Usage: tf <parse|check|canon|emit|manifest|fmt|show> <flow.tf> [--out path] [--lang ts|rs] [--write|-w].
* `tf parse` → emit canonical IR JSON for a flow.
* `tf check` → validate effects and region fences using the current catalog.
* `tf canon` → apply registered algebraic laws for normalization.
* `tf emit --lang ts|rs` → generate runnable scaffolding in the requested language.

## Examples

### app_order_publish.tf
```tf
seq{
  publish(topic="orders", key="o-1", payload="{}");
  emit-metric(name="sent")
}
```

### auth_missing.tf
```tf
sign-data(key="k1")
```

### auth_ok.tf
```tf
authorize(scope="kms.sign"){ sign-data(key="k1") }
```

### auth_wrong_scope.tf
```tf
authorize(scope="kms.decrypt"){ sign-data(key="k1") }
```

### crypto_sign_verify.tf
```tf
authorize(scope="kms.sign"){
  seq{
    sign-data(key="k1", payload="hello");
    verify-signature(key="k1", payload="hello", signature="iKqz7ejTrflNJquQ07r9SiCDBww7zOnAFO4EpEOEfAs=")
  }
}
```

### emit_commute.tf
```tf
emit-metric(key="ok") |> hash
```

### info_roundtrip.tf
```tf
serialize |> deserialize
```

### manifest_publish.tf
```tf
publish(topic="orders", key="abc", payload="{}")
```

### manifest_storage.tf
```tf
seq{
  write-object(uri="res://kv/bucket", key="z", value="1");
  read-object(uri="res://kv/bucket", key="z")
}
```

### metrics_publish.tf
```tf
seq{
  emit-metric(name="flows.processed", value=2);
  publish(topic="flows", key="demo", payload="{\"ok\":true}")
}
```

### net_publish.tf
```tf
authorize{ publish(topic="orders", key="abc", payload="{}") }
```

### obs_pure_EP.tf
```tf
emit-metric |> hash
```
