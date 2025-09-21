# L0 Catalog (generated)
Primitives: 14
Effects: Pure, Observability, Network.Out, Storage.Read, Storage.Write, Crypto, Policy, Infra, Time, UI

### tf:information/deserialize@1
| Effects | Input | Output | Laws |
| --- | --- | --- | --- |
| Pure | — | — | `law:serialize-deserialize-eq-id` |

### tf:information/hash@1
| Effects | Input | Output | Laws |
| --- | --- | --- | --- |
| Pure | — | — | `law:hash-idempotent` |

### tf:information/serialize@1
| Effects | Input | Output | Laws |
| --- | --- | --- | --- |
| Pure | — | — | `law:serialize-deserialize-eq-id` |

### tf:network/acknowledge@1
| Effects | Input | Output | Laws |
| --- | --- | --- | --- |
| Network.Out | — | — | — |

### tf:network/publish@1
| Effects | Input | Output | Laws |
| --- | --- | --- | --- |
| Network.Out | — | — | — |

### tf:network/request@1
| Effects | Input | Output | Laws |
| --- | --- | --- | --- |
| Network.Out | — | — | — |

### tf:network/subscribe@1
| Effects | Input | Output | Laws |
| --- | --- | --- | --- |
| Network.In | — | — | — |

### tf:observability/emit-metric@1
| Effects | Input | Output | Laws |
| --- | --- | --- | --- |
| Observability | — | — | `law:emitmetric-commutes-with-pure` |

### tf:resource/compare-and-swap@1
| Effects | Input | Output | Laws |
| --- | --- | --- | --- |
| Storage.Write | — | `mode="write", notes="seed", uri="res://kv/<bucket>/:<key>"` | — |

### tf:resource/delete-object@1
| Effects | Input | Output | Laws |
| --- | --- | --- | --- |
| Storage.Write | — | `mode="write", notes="seed", uri="res://kv/<bucket>/:<key>"` | — |

### tf:resource/read-object@1
| Effects | Input | Output | Laws |
| --- | --- | --- | --- |
| Storage.Read | `mode="read", notes="seed", uri="res://kv/<bucket>/:<key>"` | — | — |

### tf:resource/write-object@1
| Effects | Input | Output | Laws |
| --- | --- | --- | --- |
| Storage.Write | — | `mode="write", notes="seed", uri="res://kv/<bucket>/:<key>"` | — |

### tf:security/sign-data@1
| Effects | Input | Output | Laws |
| --- | --- | --- | --- |
| Crypto | — | — | — |

### tf:security/verify-signature@1
| Effects | Input | Output | Laws |
| --- | --- | --- | --- |
| Crypto | — | — | — |
