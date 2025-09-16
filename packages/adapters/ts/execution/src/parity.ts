import { mkdtempSync, rmSync, readFileSync } from "node:fs";
import { tmpdir } from "node:os";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { spawnSync } from "node:child_process";
import { mkdir, writeFile } from "node:fs/promises";

import { canonicalJson, executeSpec, loadSpec } from "./index.js";

const here = path.dirname(fileURLToPath(import.meta.url));
const specPath = path.join(here, "../fixtures/sample-spec.json");
const repoRoot = path.resolve(here, "../../../../..");
const outDir = path.join(repoRoot, "out/t2");
const parityPath = path.join(outDir, "adapter-parity.json");
const manifestPath = path.join(repoRoot, "crates/Cargo.toml");

const spec = await loadSpec(specPath);
const tsTrace = executeSpec(spec);

const tmpDir = mkdtempSync(path.join(tmpdir(), "adapter-parity-"));
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
    specPath,
    rustOut,
  ],
  { stdio: "inherit", cwd: repoRoot }
);

if (cargo.status !== 0) {
  rmSync(tmpDir, { recursive: true, force: true });
  throw new Error("cargo run failed");
}

const rustTrace = JSON.parse(readFileSync(rustOut, "utf-8"));
const equal = canonicalJson(tsTrace) === canonicalJson(rustTrace);

await mkdir(outDir, { recursive: true });
await writeFile(parityPath, canonicalJson({ equal, tsTrace, rustTrace }), "utf-8");

if (!equal) {
  throw new Error("adapter parity failed");
}

rmSync(tmpDir, { recursive: true, force: true });
