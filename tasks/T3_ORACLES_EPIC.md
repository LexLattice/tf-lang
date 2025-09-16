# T3_ORACLES_EPIC — Conservation • Idempotence • Transport

Covers: **T3_1** Conservation, **T3_2** Idempotence, **T3_3** Transport (round‑trip), **T3_4** Parity & contracts, **T3_5** CI & docs.

## Acceptance

### Evidence (artifacts)
- `out/t3/conservation/report.json`
- `out/t3/idempotence/report.json`
- `out/t3/transport/report.json`
- `out/t3/parity/conservation.json`
- `out/t3/parity/idempotence.json`
- `out/t3/parity/transport.json`

All canonical and deterministic (run twice, identical bytes).

### Packages/Crates
- TS: `packages/oracles/{conservation,idempotence,transport}` with README, fixtures, tests.
- Rust: `crates/oracles/{conservation,idempotence,transport}` with tests mirroring TS fixtures.

### Policies
- Determinism; no runtime deps; TS ESM `.js` suffix; no deep imports; no `as any`.
- Rust no panics in libs; prefer `Result`; sorted via `BTree*`.

### CI jobs (authoritative names)
- `t3-conservation-ts` / `t3-conservation-rust`
- `t3-idempotence-ts` / `t3-idempotence-rust`
- `t3-transport-ts` / `t3-transport-rust`
- `t3-parity` (asserts all three reports match TS↔Rust structurally)
Each job uploads artifacts under `out/t3/**`. Determinism re-run step included.

## Semantics (informal)
- **Conservation:** Compare “before” vs “after” counts/maps for declared keys; report violations (unexpected loss/gain). Input schema example in docs/oracles/conservation.md.
- **Idempotence:** Re-apply operation to its own output; results must be equal under canonical JSON (within an allowed tolerance set); report mismatch pairs.
- **Transport:** Serialize→deserialize→serialize yields identical bytes (canonical JSON); cross-runtime representation equal.

## End‑Goal (workplan)
1) Implement TS oracles + fixtures + tests. Emit reports under `out/t3/<oracle>/report.json`.
2) Implement Rust counterparts aligned with TS fixtures.
3) Build parity harness (TS driver) to run both runtimes and emit `out/t3/parity/*.json` (equal=true).
4) Wire CI workflow + determinism re-run + artifact upload.
5) Update docs and PR body; ensure no policy violations.

## Blockers (merge must fail if)
- Missing `.js` suffix on internal ESM imports (TS).
- Any `as any` in production TS.
- Any panicking unwrap/expect in Rust libs.
- Artifacts not canonical or not stable across two runs.
- Parity `equal:false` for any oracle.
