Scope: B2-nits diff only

Observations
- Rust linearized flow is clear and preserves relaxed atomics; no change needed.
- TS const tuple assertion removes `as any` cleanly; ESM imports untouched.

Polish (no code changes)
- Keep as-is. No additional comments or renames add clarity here.
