import path from "node:path";
import { fileURLToPath } from "node:url";

import { generateArtifacts } from "./index.js";

const here = path.dirname(fileURLToPath(import.meta.url));
const repoRoot = path.resolve(here, "../../../..");
const tracePath = path.join(here, "../fixtures/traces.jsonl");
const outPath = path.join(repoRoot, "out/t2/trace-tags.json");

await generateArtifacts({ tracePath, outPath });
