import path from "node:path";
import { fileURLToPath } from "node:url";
import { spawnSync } from "node:child_process";
import { mkdir, readFile, writeFile } from "node:fs/promises";

import { findRepoRoot, withTmpDir } from "@tf-lang/utils";
import { canonicalJson, executeSpec, loadSpec } from "./index.js";

const here = path.dirname(fileURLToPath(import.meta.url));
const specPath = path.join(here, "../fixtures/sample-spec.json");
const repoRoot = findRepoRoot(fileURLToPath(new URL(".", import.meta.url)));
const outDir = path.join(repoRoot, "out/t2");
const parityPath = path.join(outDir, "adapter-parity.json");
const manifestPath = path.join(repoRoot, "crates/Cargo.toml");

const spec = await loadSpec(specPath);
const tsTrace = executeSpec(spec);

const rustTrace = await withTmpDir("adapter-parity-", async (tmpDir) => {
  const rustOut = path.join(tmpDir, "rust-trace.json");

  const cargo = spawnSync(
    "cargo",
    [
      "run",
      "--manifest-path",
      manifestPath,
      "--bin",
      "dump",
      "--",
      "--spec",
      specPath,
      "--out",
      rustOut,
    ],
    { stdio: "inherit", cwd: repoRoot }
  );

  if (cargo.status !== 0) {
    throw new Error("cargo run failed");
  }

  const rustText = await readFile(rustOut, "utf-8");
  return JSON.parse(rustText) as unknown;
});

const equal = canonicalJson(tsTrace) === canonicalJson(rustTrace);

await mkdir(outDir, { recursive: true });
await writeFile(parityPath, canonicalJson({ equal, tsTrace, rustTrace }), "utf-8");

if (!equal) {
  throw new Error("adapter parity failed");
}
