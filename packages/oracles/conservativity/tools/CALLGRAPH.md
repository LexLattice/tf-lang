# CALL Graph Tool (TS)

Goal: emit a simple call graph JSON that highlights edges crossing a CALL gate.
- Entry: CLI `node tools/callgraph.ts --src packages/**/src --out out/t1/callgraph.json`
- Implementation: use TypeScript compiler API; ignore unresolved imports; emit `{nodes:[{id,file}],edges:[{from,to,kind}]}`.
- CI: run in `conservativity-oracle` job; attach `out/t1/callgraph.json`.
