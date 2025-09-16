import { canonicalJson, escapeHtml } from "@tf-lang/utils";
import { readFile, writeFile, mkdir } from "node:fs/promises";
import path from "node:path";

export { canonicalJson } from "@tf-lang/utils";

export interface TraceTag {
  spec: string;
  version: string;
  stepIndex: number;
  op: string;
  tag: string;
  metadata: Record<string, unknown>;
}

export interface CoverageByTag {
  count: number;
  specs: string[];
  steps: Array<{ spec: string; stepIndex: number }>;
}

export interface CoverageBySpec {
  tags: number;
  coveredOps: string[];
}

export interface CoverageReport {
  generatedAt: string;
  totals: {
    tags: number;
    specs: number;
    tagKinds: number;
  };
  byTag: Record<string, CoverageByTag>;
  specs: Record<string, CoverageBySpec>;
}

export interface CoverageOptions {
  generatedAt?: string;
}

export function computeCoverage(tags: TraceTag[], options: CoverageOptions = {}): CoverageReport {
  const tagMap = new Map<string, CoverageByTag>();
  const specMap = new Map<string, { tags: number; ops: Set<string> }>();

  tags.forEach((tag) => {
    const entry = tagMap.get(tag.tag) ?? { count: 0, specs: [], steps: [] };
    entry.count += 1;
    if (!entry.specs.includes(tag.spec)) {
      entry.specs.push(tag.spec);
    }
    entry.steps.push({ spec: tag.spec, stepIndex: tag.stepIndex });
    tagMap.set(tag.tag, entry);

    const specEntry = specMap.get(tag.spec) ?? { tags: 0, ops: new Set<string>() };
    specEntry.tags += 1;
    specEntry.ops.add(tag.op);
    specMap.set(tag.spec, specEntry);
  });

  const byTag: Record<string, CoverageByTag> = {};
  Array.from(tagMap.entries())
    .sort(([a], [b]) => a.localeCompare(b))
    .forEach(([tag, entry]) => {
      entry.specs.sort();
      entry.steps.sort((x, y) => x.stepIndex - y.stepIndex || x.spec.localeCompare(y.spec));
      byTag[tag] = entry;
    });

  const specs: Record<string, CoverageBySpec> = {};
  Array.from(specMap.entries())
    .sort(([a], [b]) => a.localeCompare(b))
    .forEach(([specName, entry]) => {
      specs[specName] = {
        tags: entry.tags,
        coveredOps: Array.from(entry.ops).sort(),
      };
    });

  return {
    generatedAt: options.generatedAt ?? "1970-01-01T00:00:00.000Z",
    totals: {
      tags: tags.length,
      specs: specMap.size,
      tagKinds: tagMap.size,
    },
    byTag,
    specs,
  };
}

export async function loadTags(filePath: string): Promise<TraceTag[]> {
  const text = await readFile(filePath, "utf-8");
  const parsed = JSON.parse(text);
  if (!Array.isArray(parsed)) {
    throw new Error("tags file must be an array");
  }
  return parsed as TraceTag[];
}

function coverageHtml(report: CoverageReport): string {
  const rows = Object.entries(report.byTag)
    .map(([tag, info]) => {
      const safeTag = escapeHtml(tag);
      const safeSpecs = escapeHtml(info.specs.join(", "));
      return `<tr><td>${safeTag}</td><td>${info.count}</td><td>${safeSpecs}</td></tr>`;
    })
    .join("");
  const generatedAt = escapeHtml(report.generatedAt);
  return `<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8" />
<title>TF Coverage</title>
<style>
  body { font-family: system-ui, sans-serif; padding: 1.5rem; }
  table { border-collapse: collapse; width: 100%; }
  th, td { border: 1px solid #ccc; padding: 0.5rem; text-align: left; }
  th { background: #f5f5f5; }
</style>
</head>
<body>
<h1>TF Coverage</h1>
<p>Generated at ${generatedAt}</p>
<table>
<thead><tr><th>Tag</th><th>Count</th><th>Specs</th></tr></thead>
<tbody>${rows}</tbody>
</table>
</body>
</html>
`;
}

export interface ArtifactOptions {
  tagPath?: string;
  outDir?: string;
}

export async function generateCoverageArtifacts(options: ArtifactOptions = {}): Promise<void> {
  const tagPath = options.tagPath ?? path.resolve("out/t2/trace-tags.json");
  const tags = await loadTags(tagPath);
  const report = computeCoverage(tags);
  const outDir = options.outDir ?? path.resolve("out/t2");
  await mkdir(outDir, { recursive: true });
  await writeFile(path.join(outDir, "coverage.json"), canonicalJson(report), "utf-8");
  await writeFile(path.join(outDir, "coverage.html"), coverageHtml(report), "utf-8");
}
