import path from "node:path";
import { fileURLToPath } from "node:url";

import { defineConfig } from "vitest/config";

const thisDir = path.dirname(fileURLToPath(import.meta.url));

export default defineConfig({
  resolve: {
    alias: {
      "@tf/oracles-core": path.resolve(thisDir, "../core/src/index.ts"),
    },
  },
});
