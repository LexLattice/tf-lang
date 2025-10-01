#!/usr/bin/env node
import { accessSync, constants } from "node:fs";
import path from "node:path";

const root = process.cwd();

const checks = [
  path.join(root, "packages/tf-plan/dist/cli.js"),
  path.join(root, "packages/tf-plan-compare/dist/cli.js"),
  path.join(root, "packages/tf-plan-scaffold/dist/cli.js"),
];

const missing = checks.filter((file) => {
  try {
    accessSync(file, constants.R_OK);
    return false;
  } catch {
    return true;
  }
});

if (missing.length > 0) {
  console.warn("[verify-dist] Missing build artefacts:\n - " + missing.join("\n - "));
  console.warn("Rebuild them with 'pnpm --filter @tf-lang/tf-plan* run build'.");
} else {
  console.log("[verify-dist] @tf-lang CLI dist outputs are present.");
}
