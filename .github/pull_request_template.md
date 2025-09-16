# T3 Oracles Epic — PR Report

> Fill all sections. CI will fail if required headings are missing.

## Summary
- Scope: (e.g., T3_1..T3_5)
- Key outcomes in this PR:
  - [ ] Conservation oracle (TS/Rust)
  - [ ] Idempotence oracle (TS/Rust)
  - [ ] Transport oracle (TS/Rust)
  - [ ] Parity reports (equal = true)
  - [ ] CI wiring + determinism re‑run

## Evidence (artifacts)
- [ ] `out/t3/conservation/report.json`
- [ ] `out/t3/idempotence/report.json`
- [ ] `out/t3/transport/report.json`
- [ ] `out/t3/parity/conservation.json`
- [ ] `out/t3/parity/idempotence.json`
- [ ] `out/t3/parity/transport.json`

## Determinism & Seeds
- Repeats: 2
- Seeds: <paths>
- Notes: <any caveats>

## Tests & CI
- TS tests: passed X / failed Y
- Rust tests: passed X / failed Y
- CI jobs: list status or link to checks

## Implementation Notes
- ABI / paths unchanged? Y/N (explain if N)
- Runtime deps added? (**No**) 
- Policy compliance: .js ESM suffixes, no deep imports, no `as any`, Rust panic‑free

## Hurdles / Follow-ups
- Known gaps:
- Suggested next steps:
