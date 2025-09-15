# Claims API (TypeScript)

This package exposes the TypeScript implementation of the claims API used in
local demos and integration tests. Runtime behaviour mirrors the SQLite-backed
service shipped with the winner branch.

## Type stubs

Until we land upstream typings we vendor minimal ambient declarations under
`src/types/` for `sql.js` and `@tf-lang/d1-sqlite`. These stubs keep the
monorepo TypeScript build green without introducing new runtime dependencies.
Replace them with published type definitions once they are available.

## TODO

- [ ] Replace ambient sql.js types
- [ ] Replace ambient @tf-lang/d1-sqlite types
