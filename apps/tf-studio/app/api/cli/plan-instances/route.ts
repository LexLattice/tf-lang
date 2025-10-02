import { NextResponse } from "next/server";
import { pathToFileURL } from "node:url";
import path from "node:path";
import fs from "node:fs/promises";

import { examplesRoot, repoRoot, resolveUnder } from "../_lib/safe";

export const runtime = "nodejs";
export const dynamic = "force-dynamic";

function sortObject<T>(obj: Record<string, T>, mapFn: (value: T) => T) {
  return Object.fromEntries(
    Object.keys(obj)
      .sort()
      .map((key) => [key, mapFn(obj[key])])
  );
}

function finalizeSummary(map: Record<string, any>) {
  return sortObject(map, (value) => ({
    total: value.total,
    instances: sortObject(value.instances, (count) => count),
  }));
}

export async function POST(req: Request) {
  try {
    const body = await req.json();
    const filePath = body?.filePath as string | undefined;
    const groupBy = (body?.groupBy as string | undefined) || "domain";
    const registryPath = body?.registryPath as string | undefined;
    if (!filePath) {
      return NextResponse.json({ error: "filePath required" }, { status: 400 });
    }

    const absFile = resolveUnder(examplesRoot, filePath);
    const resolveRelative = (candidate?: string) =>
      candidate ? path.resolve(repoRoot, candidate) : undefined;

    const registryFile = resolveRelative(registryPath);

    const resolverPath = path.join(repoRoot, "packages", "expander", "resolve.mjs");
    const { default: annotateInstances, normalizeChannel } = await import(
      /* webpackIgnore: true */ pathToFileURL(resolverPath).href
    );

    const raw = await fs.readFile(absFile, "utf8");
    const doc = JSON.parse(raw);
    const nodes = Array.isArray(doc.nodes) ? JSON.parse(JSON.stringify(doc.nodes)) : [];

    const registry = registryFile
      ? JSON.parse(await fs.readFile(registryFile, "utf8"))
      : undefined;

    annotateInstances({ nodes, registry });

    const domains: Record<string, any> = {};
    const schemes: Record<string, any> = {};

    for (const node of nodes) {
      const domain = node.runtime?.domain ?? "default";
      const instance = node.runtime?.instance ?? "@Memory";
      const channel = typeof node.channel === "string" ? node.channel : "";
      const normalized = normalizeChannel(channel);
      const scheme = !normalized
        ? "none"
        : normalized.startsWith("@")
          ? "dynamic"
          : normalized.split(":")[0] === "rpc"
            ? `rpc:${normalized.split(":")[1]?.split(":")[0] ?? ""}`
            : normalized.split(":")[0];

      if (!domains[domain]) domains[domain] = { total: 0, instances: {} };
      if (!schemes[scheme]) schemes[scheme] = { total: 0, instances: {} };

      domains[domain].total += 1;
      schemes[scheme].total += 1;

      domains[domain].instances[instance] = (domains[domain].instances[instance] || 0) + 1;
      schemes[scheme].instances[instance] = (schemes[scheme].instances[instance] || 0) + 1;
    }

    const summary =
      groupBy === "domain"
        ? { domains: finalizeSummary(domains), channels: finalizeSummary(schemes) }
        : { schemes: finalizeSummary(schemes), domains: finalizeSummary(domains) };

    return NextResponse.json(summary);
  } catch (err: any) {
    return NextResponse.json({ error: err?.message ?? String(err) }, { status: 500 });
  }
}
