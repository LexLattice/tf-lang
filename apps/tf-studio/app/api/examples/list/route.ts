import { NextResponse } from "next/server";
import fs from "node:fs/promises";
import path from "node:path";

import { repoRoot } from "../../cli/_lib/safe";

export const runtime = "nodejs";
export const dynamic = "force-dynamic";

export async function POST(req: Request) {
  try {
    let payload: any = {};
    try {
      payload = await req.json();
    } catch {
      payload = {};
    }

    const version = payload?.version || "v0.6";
    const buildDir = path.join(repoRoot, "examples", version, "build");
    const items: Array<{ id: string; title: string; kind: string; l0Path: string }> = [];

    try {
      const entries = await fs.readdir(buildDir);
      for (const entry of entries) {
        if (!entry.endsWith(".l0.json")) continue;
        const abs = path.join(buildDir, entry);
        try {
          const raw = await fs.readFile(abs, "utf8");
          const doc = JSON.parse(raw);
          const id = typeof doc?.pipeline_id === "string" && doc.pipeline_id.length > 0
            ? doc.pipeline_id
            : entry.replace(/\.l0\.json$/, "");
          items.push({
            id,
            title: id,
            kind: "pipeline",
            l0Path: path.relative(repoRoot, abs).replace(/\\/g, "/"),
          });
        } catch {
          // ignore malformed entries
        }
      }
    } catch {
      // directory might not exist yet; return empty list
    }

    return NextResponse.json({ items });
  } catch (err: any) {
    return NextResponse.json({ error: err?.message ?? String(err) }, { status: 500 });
  }
}
