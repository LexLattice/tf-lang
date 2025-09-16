import path from "node:path";
import { fileURLToPath } from "node:url";

import { findRepoRoot } from "@tf-lang/utils";

import { generateCoverageArtifacts } from "./index.js";

const here = path.dirname(fileURLToPath(import.meta.url));
const repoRoot = findRepoRoot(new URL(".", import.meta.url).pathname);

await generateCoverageArtifacts({
  tagPath: path.join(repoRoot, "out/t2/trace-tags.json"),
  outDir: path.join(repoRoot, "out/t2"),
});
