import { NextResponse } from "next/server";
import { pathToFileURL } from "node:url";
import path from "node:path";

import { examplesRoot, repoRoot, resolveUnder } from "../_lib/safe";

export const runtime = "nodejs";
export const dynamic = "force-dynamic";

export async function POST(req: Request) {
  try {
    const body = await req.json();
    const filePath = body?.filePath as string | undefined;
    const adaptersPath = body?.adaptersPath as string | undefined;
    if (!filePath) {
      return NextResponse.json({ error: "filePath required" }, { status: 400 });
    }

    const absFile = resolveUnder(examplesRoot, filePath);
    const registryPath = adaptersPath ? path.resolve(repoRoot, adaptersPath) : undefined;

    const typecheckPath = path.join(repoRoot, "packages", "typechecker", "typecheck.mjs");
    const { typecheckFile } = await import(
      /* webpackIgnore: true */ pathToFileURL(typecheckPath).href
    );

    const report = await typecheckFile(absFile, { registryPath });
    return NextResponse.json(report);
  } catch (err: any) {
    return NextResponse.json({ error: err?.message ?? String(err) }, { status: 500 });
  }
}
