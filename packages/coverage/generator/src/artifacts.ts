import { findRepoRoot } from "@tf-lang/utils";
import path from "node:path";
import { fileURLToPath } from "node:url";

import { generateCoverageArtifacts } from "./index.js";

const here = path.dirname(fileURLToPath(import.meta.url));
const repoRoot = findRepoRoot(fileURLToPath(new URL(".", import.meta.url)));

await generateCoverageArtifacts({
  tagPath: path.join(repoRoot, "out/t2/trace-tags.json"),
  outDir: path.join(repoRoot, "out/t2"),
});
