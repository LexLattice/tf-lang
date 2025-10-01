import { NextResponse } from "next/server";
import { pathToFileURL } from "node:url";
import path from "node:path";

import { repoRoot } from "../_lib/safe";

export const runtime = "nodejs";
export const dynamic = "force-dynamic";

export async function POST(req: Request) {
  try {
    const body = await req.json();
    const l2Yaml = body?.l2Yaml as string | undefined;
    if (!l2Yaml || l2Yaml.trim().length === 0) {
      return NextResponse.json({ error: "l2Yaml required" }, { status: 400 });
    }

    const expanderPath = path.join(repoRoot, "packages", "expander", "expand.mjs");
    const mod: any = await import(
      /* webpackIgnore: true */ pathToFileURL(expanderPath).href
    );
    const expand = mod.expandPipelineFromYaml || mod.expandPipelineFromFile || mod.expandPipeline;
    if (typeof expand !== "function") {
      return NextResponse.json({ error: "expander not available" }, { status: 500 });
    }

    const l0 = await expand(l2Yaml, {});
    return NextResponse.json({ l0 });
  } catch (err: any) {
    return NextResponse.json({ error: err?.message ?? String(err) }, { status: 500 });
  }
}
