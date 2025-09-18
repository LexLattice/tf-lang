# T3 — Synthesis Input

| Label | PR | Link | State |
|--:|--:|:--|:-----|

### Diff Similarity Summary

- Per-PR changed lines: A:699,B:645,C:718,D:677
- Common across all: 593/868 (68.3%)
- Pairwise Jaccard similarity (intersection/union):
  - A ↔ B: 82.4% (607/737)
  - A ↔ C: 80.3% (631/786)
  - A ↔ D: 81.5% (618/758)
  - B ↔ C: 78.4% (599/764)
  - B ↔ D: 83.9% (603/719)
  - C ↔ D: 80.0% (620/775)
| A | #118 | https://github.com/LexLattice/tf-lang/pull/118 | OPEN |

---

## Run A — PR #118 — feat: add canonical JSON equality core

### PR Body

# T1 Oracles Epic — Proof PR

## Summary
- Implemented shared canonical JSON/equality helpers for TS & Rust oracles.
- Re-exported canonical helpers for workspace utilities.
- Hardened canonicalization to reject non-JSON values and exposed pretty canonical JSON outputs in both runtimes.

## Evidence (artifacts)
- [ ] out/t1/oracles-report.json
- [ ] out/t1/determinism/report.json
- [ ] out/t1/conservation/report.json
- [ ] out/t1/idempotence/report.json
- [ ] out/t1/transport/report.json
- [ ] out/t1/region-visualizer.zip
- [ ] out/t1/conservativity/report.json
- [ ] out/t1/mutation-matrix.json
- [ ] out/t1/coverage.html
- [ ] out/t1/harness-seeds.jsonl
- [ ] out/t1/certificate.json (+ .sha256 files)

## Determinism & Seeds
- Repeats: pending
- Seeds: pending
- First failing seeds (if any): pending

## Tests & CI
- TS tests: `pnpm -C packages/oracles/core test`, `pnpm -C packages/utils test`
- Rust tests: `cargo test --workspace --all-targets --manifest-path crates/Cargo.toml`
- Proof Kit check: pending
- CI jobs: pending

## Implementation Notes
- ABI unchanged; canonical helpers now cover map/set/pointer semantics.
- Policy compliance: ESM .js imports, no deep cross-package imports, Rust no panics.

## Hurdles / Follow-ups
- Remaining oracles, harness, mutation, and artifacts still to be implemented.


------
https://chatgpt.com/codex/tasks/task_e_68c9ee6f9fa483209f529efedd7aeb57

### AI Comments (issue)


### AI Review Comments (inline)

| B | #119 | https://github.com/LexLattice/tf-lang/pull/119 | OPEN |

---

## Run B — PR #119 — feat: add canonical JSON equality core

### PR Body

# T1 Oracles Epic — Proof PR

## Summary
- Implemented shared canonical JSON/equality helpers for TS & Rust oracles.
- Re-exported canonical helpers for workspace utilities.
- Hardened canonical JSON helpers to reject non-JSON inputs, preserve container ordering, and expose prettyCanonicalJson for reports.

## Evidence (artifacts)
- [ ] out/t1/oracles-report.json
- [ ] out/t1/determinism/report.json
- [ ] out/t1/conservation/report.json
- [ ] out/t1/idempotence/report.json
- [ ] out/t1/transport/report.json
- [ ] out/t1/region-visualizer.zip
- [ ] out/t1/conservativity/report.json
- [ ] out/t1/mutation-matrix.json
- [ ] out/t1/coverage.html
- [ ] out/t1/harness-seeds.jsonl
- [ ] out/t1/certificate.json (+ .sha256 files)

## Determinism & Seeds
- Repeats: pending
- Seeds: pending
- First failing seeds (if any): pending

## Tests & CI
- TS tests: `pnpm -C packages/oracles/core test`, `pnpm -C packages/utils test`
- Rust tests: `cargo test --workspace --all-targets --manifest-path crates/Cargo.toml`
- Proof Kit check: pending
- CI jobs: pending

## Implementation Notes
- ABI unchanged; canonical helpers now cover map/set/pointer semantics.
- Policy compliance: ESM .js imports, no deep cross-package imports, Rust no panics.

## Hurdles / Follow-ups
- Remaining oracles, harness, mutation, and artifacts still to be implemented.


------
https://chatgpt.com/codex/tasks/task_e_68c9ee6f9fa483209f529efedd7aeb57

### AI Comments (issue)


### AI Review Comments (inline)

| C | #120 | https://github.com/LexLattice/tf-lang/pull/120 | OPEN |

---

## Run C — PR #120 — fix: harden canonical helpers

### PR Body

# T1 Oracles Epic — Proof PR

## Summary
- Hardened shared canonical JSON/equality helpers for TS & Rust oracles, rejecting non-JSON inputs and adding pretty printers.
- Re-exported canonical helpers for workspace utilities.

## Evidence (artifacts)
- [ ] out/t1/oracles-report.json
- [ ] out/t1/determinism/report.json
- [ ] out/t1/conservation/report.json
- [ ] out/t1/idempotence/report.json
- [ ] out/t1/transport/report.json
- [ ] out/t1/region-visualizer.zip
- [ ] out/t1/conservativity/report.json
- [ ] out/t1/mutation-matrix.json
- [ ] out/t1/coverage.html
- [ ] out/t1/harness-seeds.jsonl
- [ ] out/t1/certificate.json (+ .sha256 files)

## Determinism & Seeds
- Repeats: pending
- Seeds: pending
- First failing seeds (if any): pending

## Tests & CI
- TS tests: `pnpm -C packages/oracles/core test`, `pnpm -C packages/utils test`
- Rust tests: `cargo test --workspace --all-targets --manifest-path crates/Cargo.toml`
- Proof Kit check: pending
- CI jobs: pending

## Implementation Notes
- ABI unchanged; canonical helpers now reject non-JSON values and expose pretty JSON formatting.
- Policy compliance: ESM .js imports, no deep cross-package imports, Rust no panics.

## Hurdles / Follow-ups
- Remaining oracles, harness, mutation, and artifacts still to be implemented.


------
https://chatgpt.com/codex/tasks/task_e_68c9ee6f9fa483209f529efedd7aeb57

### AI Comments (issue)


### AI Review Comments (inline)

| D | #121 | https://github.com/LexLattice/tf-lang/pull/121 | OPEN |

---

## Run D — PR #121 — fix: harden canonical json helpers

### PR Body

# T1 Oracles Epic — Proof PR

## Summary
- Implemented shared canonical JSON/equality helpers for TS & Rust oracles.
- Re-exported canonical helpers for workspace utilities.
- Hardened canonicalization to reject non-JSON inputs and added pretty canonical JSON formatting for reports.

## Evidence (artifacts)
- [ ] out/t1/oracles-report.json
- [ ] out/t1/determinism/report.json
- [ ] out/t1/conservation/report.json
- [ ] out/t1/idempotence/report.json
- [ ] out/t1/transport/report.json
- [ ] out/t1/region-visualizer.zip
- [ ] out/t1/conservativity/report.json
- [ ] out/t1/mutation-matrix.json
- [ ] out/t1/coverage.html
- [ ] out/t1/harness-seeds.jsonl
- [ ] out/t1/certificate.json (+ .sha256 files)

## Determinism & Seeds
- Repeats: pending
- Seeds: pending
- First failing seeds (if any): pending

## Tests & CI
- TS tests: `pnpm -C packages/oracles/core test`, `pnpm -C packages/utils test`
- Rust tests: `cargo test --workspace --all-targets --manifest-path crates/Cargo.toml`
- Proof Kit check: pending
- CI jobs: pending

## Implementation Notes
- ABI unchanged; canonical helpers now cover map/set/pointer semantics.
- Policy compliance: ESM .js imports, no deep cross-package imports, Rust no panics.

## Hurdles / Follow-ups
- Remaining oracles, harness, mutation, and artifacts still to be implemented.


------
https://chatgpt.com/codex/tasks/task_e_68c9ee6f9fa483209f529efedd7aeb57

### AI Comments (issue)


### AI Review Comments (inline)

