# L0 Catalog (generated)
Primitives: 14
Effects: Pure, Observability, Network.Out, Storage.Read, Storage.Write, Crypto, Policy, Infra, Time, UI

### tf:information/deserialize@1

| Field | Value |
| --- | --- |
| Effects | `Pure` |
| Input | None |
| Output | None |
| Laws | `law:serialize-deserialize-eq-id` |

### tf:information/hash@1

| Field | Value |
| --- | --- |
| Effects | `Pure` |
| Input | None |
| Output | None |
| Laws | `law:hash-idempotent` |

### tf:information/serialize@1

| Field | Value |
| --- | --- |
| Effects | `Pure` |
| Input | None |
| Output | None |
| Laws | `law:serialize-deserialize-eq-id` |

### tf:network/acknowledge@1

| Field | Value |
| --- | --- |
| Effects | `Network.Out` |
| Input | None |
| Output | None |
| Laws | None |

### tf:network/publish@1

| Field | Value |
| --- | --- |
| Effects | `Network.Out` |
| Input | None |
| Output | None |
| Laws | None |

### tf:network/request@1

| Field | Value |
| --- | --- |
| Effects | `Network.Out` |
| Input | None |
| Output | None |
| Laws | None |

### tf:network/subscribe@1

| Field | Value |
| --- | --- |
| Effects | `Network.In` |
| Input | None |
| Output | None |
| Laws | None |

### tf:observability/emit-metric@1

| Field | Value |
| --- | --- |
| Effects | `Observability` |
| Input | None |
| Output | None |
| Laws | `law:emitmetric-commutes-with-pure` |

### tf:resource/compare-and-swap@1

| Field | Value |
| --- | --- |
| Effects | `Storage.Write` |
| Input | None |
| Output | mode=write, uri=res://kv/<bucket>/:<key>, notes=seed |
| Laws | None |

### tf:resource/delete-object@1

| Field | Value |
| --- | --- |
| Effects | `Storage.Write` |
| Input | None |
| Output | mode=write, uri=res://kv/<bucket>/:<key>, notes=seed |
| Laws | None |

### tf:resource/read-object@1

| Field | Value |
| --- | --- |
| Effects | `Storage.Read` |
| Input | mode=read, uri=res://kv/<bucket>/:<key>, notes=seed |
| Output | None |
| Laws | None |

### tf:resource/write-object@1

| Field | Value |
| --- | --- |
| Effects | `Storage.Write` |
| Input | None |
| Output | mode=write, uri=res://kv/<bucket>/:<key>, notes=seed |
| Laws | None |

### tf:security/sign-data@1

| Field | Value |
| --- | --- |
| Effects | `Crypto` |
| Input | None |
| Output | None |
| Laws | None |

### tf:security/verify-signature@1

| Field | Value |
| --- | --- |
| Effects | `Crypto` |
| Input | None |
| Output | None |
| Laws | None |
