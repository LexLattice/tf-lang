# Track E — Proofs Quickstart

Emit the Alloy/SMT suite and sync manifests so the optimizer coverage gate stays green.

## Prerequisites

- Tracks A–D complete (ensures manifests under `out/0.5/proofs/**`)
- `pnpm -w -r build` to make proof emitters available
- Optional: Z3 on `PATH` for richer `ci-gate` checks (not required)

## Commands (3–7 steps)

```bash
OUT=out/0.5/proofs
pnpm run proofs:emit
mkdir -p "$OUT"
# Temporary shim: proofs:emit still targets out/0.4; copy forward until the emitter writes to 0.5 directly.
cp -R out/0.4/proofs/. "$OUT"/
head -n 5 "$OUT/storage_ok.smt2"
pnpm run proofs:coverage
```

## Expected output

```
wrote /workspace/tf-lang/out/0.4/proofs/storage_ok.smt2
...
(assert true)
(check-sat)
{
  "ok": true,
  "missing": [],
  "covered": []
}
```

*Keep the `out/0.5/proofs/**` mirror up to date—the coverage gate scans that directory for manifests and confirms every law has a committed stub.*

## Where next?

- Proof artifact layout & gates: [`docs/proofs/README.md`](../../proofs/README.md)
- Adding new obligations: [`docs/l0-effects-lattice.md`](../../l0-effects-lattice.md)
- Registry maintenance checklist: [`docs/proofs/README.md#law-stubs-scriptsproofslaws`](../../proofs/README.md#law-stubs-scriptsproofslaws)

> **Troubleshooting**
>
> - `Error: spawn z3 ENOENT` – the emit scripts succeed without Z3; install it only if you need solver validation locally.
> - Copy step complains about missing `out/0.4/proofs` – rerun `pnpm run proofs:emit`; it creates the source directory.
> - Coverage reports missing laws – ensure optimizer manifests (Track D) were copied into `out/0.5/proofs/` before invoking `pnpm run proofs:coverage`.
