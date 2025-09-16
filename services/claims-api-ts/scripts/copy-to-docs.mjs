import { mkdir, rm, cp } from "node:fs/promises";
import { fileURLToPath } from "node:url";
import path from "node:path";

const here = path.dirname(fileURLToPath(new URL(import.meta.url)));
const svc = path.resolve(here, "..");
const repoRoot = path.resolve(svc, "..", "..");
const dist = path.join(svc, "dist");
const docs = path.join(repoRoot, "docs", "claims");

await rm(docs, { recursive: true, force: true });
await mkdir(docs, { recursive: true });
await cp(dist, docs, { recursive: true });

const explorer = path.join(repoRoot, "docs", "claims-explorer.html");
try {
  await cp(explorer, path.join(docs, "index.html"));
} catch (err) {
  console.warn("Warning: unable to copy claims-explorer.html", err?.message ?? err);
}

const dataDir = path.join(docs, "data");
await mkdir(dataDir, { recursive: true });
const dataset = path.join(repoRoot, "docs", "data", "claims-ro-mini.json");
try {
  await cp(dataset, path.join(dataDir, "claims-ro-mini.json"));
} catch (err) {
  console.warn("Warning: unable to copy claims dataset", err?.message ?? err);
}

console.log("Copied", dist, "→", docs);
