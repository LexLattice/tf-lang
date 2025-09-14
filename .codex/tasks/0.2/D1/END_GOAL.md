Perspective: Synthesized (Reliability + DX)

- Claims API uses a **SQLite** adapter for counts and clause data.
- Each response includes `dataset_version` and a `query_hash` (BLAKE3 over canonical request bytes).
- Numeric counts/clauses are **stable** across repeated runs with identical input.
- Each response returns **≥ 10** distinct evidence samples.
