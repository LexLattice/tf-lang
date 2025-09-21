# L0 Catalog (generated)
Primitives: 14
Effects: Pure, Observability, Network.Out, Storage.Read, Storage.Write, Crypto, Policy, Infra, Time, UI

### tf:information/deserialize@1

| Effects | Input | Output | Laws |
| --- | --- | --- | --- |
| Pure | — | — | law:serialize-deserialize-eq-id |

### tf:information/hash@1

| Effects | Input | Output | Laws |
| --- | --- | --- | --- |
| Pure | — | — | law:hash-idempotent |

### tf:information/serialize@1

| Effects | Input | Output | Laws |
| --- | --- | --- | --- |
| Pure | — | — | law:serialize-deserialize-eq-id |

### tf:network/acknowledge@1

| Effects | Input | Output | Laws |
| --- | --- | --- | --- |
| Network.Out | — | QoS: delivery_guarantee=at-least-once, ordering=per-key | — |

### tf:network/publish@1

| Effects | Input | Output | Laws |
| --- | --- | --- | --- |
| Network.Out | — | QoS: delivery_guarantee=at-least-once, ordering=per-key | — |

### tf:network/request@1

| Effects | Input | Output | Laws |
| --- | --- | --- | --- |
| Network.Out | — | QoS: delivery_guarantee=at-least-once, ordering=per-key | — |

### tf:network/subscribe@1

| Effects | Input | Output | Laws |
| --- | --- | --- | --- |
| Network.In | — | QoS: delivery_guarantee=at-least-once, ordering=per-key | — |

### tf:observability/emit-metric@1

| Effects | Input | Output | Laws |
| --- | --- | --- | --- |
| Observability | — | — | law:emitmetric-commutes-with-pure |

### tf:resource/compare-and-swap@1

| Effects | Input | Output | Laws |
| --- | --- | --- | --- |
| Storage.Write | — | Writes: res://kv/<bucket>/:<key> (mode=write, notes=seed) | — |

### tf:resource/delete-object@1

| Effects | Input | Output | Laws |
| --- | --- | --- | --- |
| Storage.Write | — | Writes: res://kv/<bucket>/:<key> (mode=write, notes=seed) | — |

### tf:resource/read-object@1

| Effects | Input | Output | Laws |
| --- | --- | --- | --- |
| Storage.Read | Reads: res://kv/<bucket>/:<key> (mode=read, notes=seed) | — | — |

### tf:resource/write-object@1

| Effects | Input | Output | Laws |
| --- | --- | --- | --- |
| Storage.Write | — | Writes: res://kv/<bucket>/:<key> (mode=write, notes=seed) | — |

### tf:security/sign-data@1

| Effects | Input | Output | Laws |
| --- | --- | --- | --- |
| Crypto | Data classes: secrets | — | — |

### tf:security/verify-signature@1

| Effects | Input | Output | Laws |
| --- | --- | --- | --- |
| Crypto | Data classes: none | — | — |
