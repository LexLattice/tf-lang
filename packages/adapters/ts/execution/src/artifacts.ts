import { findRepoRoot } from "@tf-lang/utils";
import path from "node:path";
import { fileURLToPath } from "node:url";

import { writeTraceArtifacts } from "./index.js";

const here = path.dirname(fileURLToPath(import.meta.url));
const specPath = path.join(here, "../fixtures/sample-spec.json");
const repoRoot = findRepoRoot(new URL(".", import.meta.url).pathname);
const outDir = path.join(repoRoot, "out/t2");

await writeTraceArtifacts({ outDir, specPath });
