# L0 DSL Cheatsheet (generated)

## Basics
- Chain primitives or regions with `|>` for sequential pipelines.
- Use `seq{ ... }` blocks for multi-step sequences and `par{ ... }` for parallel branches.
- Primitives are lowercase identifiers; pipeline nodes preserve the written order.

## Args & Literals
- Arguments appear as `prim(key=value, other=123)` with comma separators.
- Strings accept single or double quotes with standard escape sequences.
- Numbers allow optional `-` prefix and fractional parts; booleans use `true` or `false`, and `null` is accepted.
- Arrays `[a, b, c]` and objects `{key: value}` are parsed recursively.

## Regions
- `authorize{ ... }` wraps a scoped block; optional `authorize(region="us"){ ... }` attributes sit in parentheses.
- `txn{ ... }` creates a transactional region with the same attribute syntax.
- Regions compose with pipelines just like primitives (`step |> authorize{ ... }`).

## Comments
- The parser does not recognize line or block comments; keep DSL files comment-free or encode notes via args.

## CLI usage
- Commands mirror `tf <parse|check|canon|emit|manifest|fmt|show> <flow.tf> [--out path] [--lang ts|rs] [--write|-w]` from `packages/tf-compose/bin/tf.mjs`.
- `tf parse <flow.tf> [-o out.json]` emits canonical IR JSON.
- `tf check <flow.tf> [-o verdict.json]` validates effects and region constraints.
- `tf canon <flow.tf> [-o canon.json]` normalizes flows with catalog laws.
- `tf emit <flow.tf> [--lang ts|rs] [--out dir]` generates runnable adapters.

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

### run_storage_ok.tf
```tf
authorize{
  seq{
    write-object(uri="res://inmem/kv", key="alpha", value="1");
    write-object(uri="res://inmem/kv", key="beta", value="2")
  }
}
```

### signing.tf
```tf
serialize |> hash |> authorize{ sign-data(key_ref="k1") }
```

### storage_conflict.tf
```tf
authorize{
  par{
    write-object(uri="res://kv/bucket", key="x", value="1");
    write-object(uri="res://kv/bucket", key="x", value="2")
  }
}
```

### storage_ok.tf
```tf
authorize{
  seq{
    write-object(uri="res://kv/bucket", key="x", value="1");
    write-object(uri="res://kv/bucket", key="y", value="2")
  }
}
```

### txn_fail_missing_key.tf
```tf
txn{
  write-object(uri="res://kv/bucket", key="x", value="1")
}
```

### write_outside_txn.tf
```tf
write-object(uri="res://kv/bucket", key="z", value="3")
```
