# @tf/oracles-conservation

Conservation oracle ensuring that declared keys retain their values between a **before** and **after** snapshot.

## Usage

```ts
import { createOracleCtx } from "@tf/oracles-core";
import { checkConservation } from "@tf/oracles-conservation";

const ctx = createOracleCtx("0xfeed", { now: 0 });
const result = await checkConservation(
  {
    keys: ["records", "warnings"],
    before: { records: 3, warnings: 0 },
    after: { records: 3, warnings: 0 },
  },
  ctx,
);
```

On success the oracle returns the number of keys checked. When mismatches occur it reports the violating keys with canonical
JSON payloads suitable for human-readable reports.
