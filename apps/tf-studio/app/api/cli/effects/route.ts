import { NextResponse } from "next/server";
import { pathToFileURL } from "node:url";
import path from "node:path";
import fs from "node:fs/promises";

import { examplesRoot, repoRoot, resolveUnder } from "../_lib/safe";

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
    const raw = await fs.readFile(absFile, "utf8");
    const doc = JSON.parse(raw);

    const modPath = path.join(repoRoot, "tools", "tf-lang-cli", "lib", "effects.mjs");
    const { summarizeEffects } = await import(
      /* webpackIgnore: true */ pathToFileURL(modPath).href
    );

    return NextResponse.json({ summary: summarizeEffects(doc) });
  } catch (err: any) {
    return NextResponse.json({ error: err?.message ?? String(err) }, { status: 500 });
  }
}
