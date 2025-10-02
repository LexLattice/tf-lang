import { NextResponse } from "next/server";
import { pathToFileURL } from "node:url";
import path from "node:path";

import { examplesRoot, policyRoot, repoRoot, resolveUnder } from "../_lib/safe";

export const runtime = "nodejs";
export const dynamic = "force-dynamic";

export async function POST(req: Request) {
  try {
    const body = await req.json();
    const filePath = body?.filePath as string | undefined;
    if (!filePath) {
      return NextResponse.json({ error: "filePath required" }, { status: 400 });
    }

    const absFile = resolveUnder(examplesRoot, filePath);
    const absPolicy = body?.policyPath ? resolveUnder(policyRoot, body.policyPath) : undefined;
    const absCaps = body?.capsPath ? resolveUnder(policyRoot, body.capsPath) : undefined;

    const checkerPath = path.join(repoRoot, "packages", "checker", "check.mjs");
    const { checkL0 } = await import(
      /* webpackIgnore: true */ pathToFileURL(checkerPath).href
    );

    const report = await checkL0(absFile, {
      policyPath: absPolicy,
      capsPath: absCaps,
    });

    return NextResponse.json(report);
  } catch (err: any) {
    return NextResponse.json({ error: err?.message ?? String(err) }, { status: 500 });
  }
}
