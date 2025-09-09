
# TF-Lang L0 (TypeScript skeleton)

Deterministic kernel for True-Function programs in TypeScript: VM, type/effect checker stubs, and core models.

## Layout
- `src/model/` — typed artifacts (bytecode, effects, ids).
- `src/vm/` — bytecode interpreter + Host interface.
- `src/check/` — checker stubs.
- `tests/` — Vitest suite (laws + smoke tests).
- `examples/` — tiny program JSON.

## Quickstart
```bash
pnpm i    # or npm i / yarn
pnpm test
```

MIT-licensed. Iterate freely.
