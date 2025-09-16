import path from "node:path";
import { fileURLToPath } from "node:url";

import { writeArtifacts } from "./index.js";

const here = path.dirname(fileURLToPath(import.meta.url));
const repoRoot = path.resolve(here, "../../..");
const defaultOut = path.join(repoRoot, "out/t2/tf-check");
const specPath = path.join(here, "../fixtures/sample-spec.json");

await writeArtifacts({ outDir: defaultOut, inputPath: specPath });
