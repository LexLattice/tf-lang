Perspective: Synthesized (Reliability + DX)

- Minimal in-memory HTTP host exposes **only** `POST /plan` and `POST /apply`.
- Repeating identical requests is **idempotent**: responses are identical and leave state unchanged.
- Journal entries in responses are **canonical** (stable ordering/bytes) and include proofs **only** when `DEV_PROOFS=1`.
- All state is **ephemeral** (lost on restart); no external persistence.
