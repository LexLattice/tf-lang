.PHONY: oracle demo

oracle:
pnpm tf-check run --mode=ci

demo:
pnpm tf-plan compare --plan out/t4/plan/plan.ndjson --inputs out/t4/scaffold/index.json --out out/t4/compare
