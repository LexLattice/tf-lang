# Proof Artifacts and Checks

This branch adds a thin gate around the proof artifacts that leave the repo. The scripts live under `scripts/proofs/` and focus on three surfaces:

- validating `used_laws` manifests emitted by the pipeline,
- reconstructing the obligations for tiny flows so we can spot missing SMT coverage quickly, and
- ensuring every law we consume has an SMT stub committed alongside the code.

## Manifest validation (`ci-gate.mjs --check-used`)

`out/**/proofs/used-laws.json` files are produced during plan compilation. Each manifest lists the canonical laws used to justify rewrites along with an optional `rewrites` array that maps proof handles to their supporting law.

Running `node scripts/proofs/ci-gate.mjs --check-used <manifest>`:

1. checks that the JSON shape matches `{ used_laws: [...], rewrites: [...]? }`,
2. canonicalises every entry and ensures it is present in `packages/tf-l0-proofs/src/smt-laws.mjs`,
3. verifies bi-directional rewrite linkage (if a `used_laws` entry advertises `rewrite`, the same handle must appear under `rewrites`, and vice-versa), and
4. reports `{ ok, missing, linked }`, where `missing` lists structural problems and `linked` counts rewrite handles that appear in both sections with the same law.

The manifests already contain canonical names, but we still trim and normalise them before comparing them to the law catalog.

## Small flow solver (`ci-gate.mjs --small`)

Small flows are authored as `seq { ... }` snippets. The solver:

1. strips comments and tokenises the primitive names,
2. infers obligations (idempotent, inverse, and commute-with-pure) using `packages/tf-opt/lib/rewrite-detect.mjs`,
3. confirms that every obligation is backed by a known law, and
4. emits `{ ok, obligations, primitives, ... }`.

If Z3 is available we also emit a `(check-sat)` query to make sure the rewritten flow is unsatisfiable. When Z3 is not on `PATH` the solver reports `{ ok: true, skipped: "z3 not found" }` so the pipeline stays green while keeping the obligation analysis intact.

## Law stubs (`scripts/proofs/laws/*.smt2`)

Every law referenced by the gate has a committed SMT stub. The filenames replace `:` with `__` to stay portable (e.g. `commute:emit-metric-with-pure` → `commute__emit-metric-with-pure.smt2`). The contents are generated via `packages/tf-l0-proofs/src/smt-laws.mjs#emitLaw` so they always reflect the latest axiom definitions.

When adding a new law:

1. extend `packages/tf-l0-proofs/src/smt-laws.mjs`,
2. regenerate the stub (`node --input-type=module -e "import { emitLaw } from './packages/tf-l0-proofs/src/smt-laws.mjs'; ..."`), and
3. rerun `scripts/proofs/coverage.mjs` to confirm the stub is picked up.

## Coverage report (`scripts/proofs/coverage.mjs`)

`node scripts/proofs/coverage.mjs` scans `out/0.5/proofs/**` for manifests, extracts every referenced law, and compares the set to the stubs under `scripts/proofs/laws/`. The script prints `{ ok, missing, covered }` to stdout, exits with status code `0` when everything is covered, and exits non-zero (with the missing list) when a manifest mentions a law without a committed stub.

The `--out <dir>` flag lets you point the script at an alternate `out` root (the default is `out/` → `out/0.5/proofs`). This is handy for tests that stage manifests in temporary directories.
