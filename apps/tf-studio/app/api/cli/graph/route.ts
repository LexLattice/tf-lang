import { NextResponse } from "next/server";
import { pathToFileURL } from "node:url";
import path from "node:path";
import fs from "node:fs/promises";
import { examplesRoot, repoRoot, resolveUnder } from "../_lib/safe";

export const runtime = "nodejs";
export const dynamic = "force-dynamic";

type GraphReq = { filePath: string; strict?: boolean };

export async function POST(req: Request) {
  try {
    const body = (await req.json()) as GraphReq;
    if (!body?.filePath) {
      return NextResponse.json({ error: "filePath required" }, { status: 400 });
    }

    // Resolve & guard: only under examples/**
    const absFile = resolveUnder(examplesRoot, body.filePath);
    if (!absFile.endsWith(".l0.json")) {
      return NextResponse.json({ error: "expected an .l0.json file" }, { status: 400 });
    }

    const raw = await fs.readFile(absFile, "utf8");
    const doc = JSON.parse(raw);

    // Dynamically import our DOT builder from the repo (no shelling out)
    const dotPath = path.join(repoRoot, "tools", "tf-lang-cli", "lib", "dot.mjs");
    const { buildDotGraph } = await import(
      /* webpackIgnore: true */ pathToFileURL(dotPath).href
    );

    const strict = body?.strict === true;
    const dot = buildDotGraph(doc, { strict });
    return NextResponse.json({ dot, file: absFile });
  } catch (err: any) {
    return NextResponse.json({ error: err?.message ?? String(err) }, { status: 500 });
  }
}
