# L0 DSL Cheatsheet (generated)

## Basics

The DSL composes primitives with the pipeline operator `|>`. A single line such as ``serialize |> hash`` creates a sequential flow.
Use `seq{ ... }` blocks to spell out multi-line sequences. Steps inside a block are separated with semicolons (`;`).
`par{ ... }` introduces parallel branches. Each branch is parsed like a standalone flow and must be terminated with a semicolon unless it is the final branch.

## Args & Literals

Arguments follow the form `prim(key=value, ...)`. Strings accept both single and double quotes and support standard escape sequences.
Numbers accept optional leading minus signs and fractional components. Bare identifiers map to lower-cased primitive IDs or literal booleans (`true`, `false`) and `null`.
Arrays (`[a, b, c]`) and objects (`{ key: value }`) are supported recursively, so complex payloads can be passed directly in-line.

## Regions

`authorize{ ... }` wraps a sub-flow that requires policy checks. Optional attributes may appear as `authorize(scope="admin"){ ... }` before the block.
`txn{ ... }` declares a transaction region. It shares the same attribute syntax as `authorize{}` and evaluates its children sequentially.

## Comments

The grammar does not include line or block comments yet. Keep flows self-documenting or maintain commentary alongside the `.tf` files.

## CLI usage

The `tf` helper under `packages/tf-compose/bin/tf.mjs` exposes the main workflows:
- `tf parse <flow.tf>` → parse and emit the canonical IR JSON.
- `tf check <flow.tf>` → run the lattice-aware checker and print the verdict JSON.
- `tf canon <flow.tf>` → normalize the IR using catalog + law data.
- `tf emit --lang ts|rs <flow.tf>` → write language-specific scaffolding into `out/0.4/codegen-*`.

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

### obs_pure_PE.tf

```tf
hash |> emit-metric
```

### par_conflict_bad.tf

```tf
par{ write-object(uri="res://kv/bucket", key="x", value="1"); write-object(uri="res://kv/bucket", key="x", value="2") }
```

### run_publish.tf

```tf
authorize{ publish(topic="events", key="event-1", payload="{}") }
```

### signing.tf

```tf
serialize |> hash |> authorize{ sign-data(key_ref="k1") }
```

### txn_fail_missing_key.tf

```tf
txn{
  write-object(uri="res://kv/bucket", key="x", value="1")
}
```

### txn_ok.tf

```tf
txn{
  compare-and-swap(uri="res://kv/bucket", key="x", value="1", ifMatch=0);
  write-object(uri="res://kv/bucket", key="y", value="2", idempotency_key="abc-123")
}
```

### write_outside_txn.tf

```tf
write-object(uri="res://kv/bucket", key="z", value="3")
```
