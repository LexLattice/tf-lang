import path from "node:path";

/** Repo root from a Next app (apps/tf-studio) */
export const repoRoot = path.resolve(process.cwd(), "..", "..");
export const examplesRoot = path.join(repoRoot, "examples");   // allow examples/v*/**
export const policyRoot   = path.join(repoRoot, "policy");     // allow policy/**

/** Resolve a candidate path and ensure it sits under the allowed root. */
export function resolveUnder(allowedRoot: string, candidate: string): string {
  const base = candidate.startsWith("/") || /^[A-Za-z]:[\\/]/.test(candidate)
    ? candidate
    : path.join(repoRoot, candidate);
  const abs  = path.resolve(base);
  const rel  = path.relative(allowedRoot, abs);
  if (rel.startsWith("..") || path.isAbsolute(rel)) {
    throw new Error(`path outside allowed root: ${candidate}`);
  }
  return abs;
}
