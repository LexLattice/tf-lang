import { NextResponse } from "next/server";
import { pathToFileURL } from "node:url";
import path from "node:path";
import { examplesRoot, policyRoot, repoRoot, resolveUnder } from "../_lib/safe";

export const runtime = "nodejs";
export const dynamic = "force-dynamic";

type LawsReq = {
  filePath: string;
  goal?: "branch-exclusive";
  maxBools?: number;
  policyPath?: string;
  capsPath?: string;
};

function collectBranchVariables(entry: any): string[] {
  const vars = new Set<string>();
  const add = (arr: any[]) =>
    (Array.isArray(arr) ? arr : []).forEach((it) => {
      const v = it?.guard?.var;
      if (typeof v === "string") vars.add(v);
    });
  add(entry?.positive);
  add(entry?.negative);
  return Array.from(vars).sort();
}

function evaluateGuard(guard: any, assignment: Record<string, boolean>): boolean {
  if (!guard || guard.kind !== "var" || typeof guard.var !== "string") return false;
  const val = Boolean(assignment[guard.var]);
  return guard.negated ? !val : val;
}

function evaluateBranchEntry(entry: any, assignment: Record<string, boolean>): boolean {
  const pos = Array.isArray(entry?.positive) ? entry.positive : [];
  const neg = Array.isArray(entry?.negative) ? entry.negative : [];
  const posActive = pos.some((it) => evaluateGuard(it?.guard, assignment));
  const negActive = neg.some((it) => evaluateGuard(it?.guard, assignment));
  return !(posActive && negActive);
}

export async function POST(req: Request) {
  try {
    const body = (await req.json()) as LawsReq;
    if (!body?.filePath) {
      return NextResponse.json({ error: "filePath required" }, { status: 400 });
    }

    const absFile   = resolveUnder(examplesRoot, body.filePath);
    const absPolicy = body.policyPath ? resolveUnder(policyRoot, body.policyPath) : undefined;
    const absCaps   = body.capsPath   ? resolveUnder(policyRoot, body.capsPath)   : undefined;

    const checkerPath = path.join(repoRoot, "packages", "checker", "check.mjs");
    const proverPath  = path.join(repoRoot, "packages", "prover", "counterexample.mjs");
    const { checkL0 } = await import(
      /* webpackIgnore: true */ pathToFileURL(checkerPath).href
    );
    const { findCounterexample } = await import(
      /* webpackIgnore: true */ pathToFileURL(proverPath).href
    );

    const report = await checkL0(absFile, {
      policyPath: absPolicy,
      capsPath: absCaps,
    });

    let counterexample: any = null;
    const goal = body.goal ?? null;
    const maxBools = Number.isInteger(body?.maxBools) ? Math.max(1, Math.min(8, body.maxBools!)) : 8;

    if (report?.status === "RED" && goal === "branch-exclusive") {
      const failing = report?.laws?.branch_exclusive?.results?.find((e: any) => e?.status === "ERROR");
      if (failing) {
        const variables = collectBranchVariables(failing);
        try {
          counterexample = findCounterexample({
            goal: "branch-exclusive",
            guard: failing.guard ?? null,
            reason: failing.reason ?? "overlap",
            variables,
            positive: failing.positive,
            negative: failing.negative,
            predicate: (candidate: Record<string, boolean>) => evaluateBranchEntry(failing, candidate),
            maxBools,
          });
        } catch {
          counterexample = null;
        }
      }
    }

    return NextResponse.json({
      status: report?.status ?? "RED",
      laws: report?.laws ?? {},
      ...(counterexample ? { counterexample } : {}),
      file: absFile,
      policyPath: absPolicy ?? null,
      capsPath: absCaps ?? null,
    });
  } catch (err: any) {
    return NextResponse.json({ error: err?.message ?? String(err) }, { status: 500 });
  }
}
