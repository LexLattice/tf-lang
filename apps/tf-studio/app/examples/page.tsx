import Link from "next/link";
import fs from "node:fs/promises";
import path from "node:path";

import ExampleCard from "../../components/ExampleCard";
import { repoRoot } from "../api/cli/_lib/safe";

async function fetchExamples() {
  const version = "v0.6";
  const buildDir = path.join(repoRoot, "examples", version, "build");
  const items: Array<{ id: string; title: string; l0Path: string }> = [];

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
          l0Path: path.relative(repoRoot, abs).replace(/\\/g, "/"),
        });
      } catch {
        // ignore malformed entries
      }
    }
  } catch {
    // directory might not exist yet; return empty list
  }

  return items;
}

const QUICK_EXAMPLES = [
  {
    title: "Auto FNOL Fast Track",
    description:
      "Canonical v0.6 build trace. Render the DOT graph or check the branch exclusivity law harness.",
    filePath: "examples/v0.6/build/auto.fnol.fasttrack.v1.l0.json",
    lawGoal: "branch-exclusive" as const,
  },
  {
    title: "Auto Quote Bind Issue",
    description:
      "A larger pipeline with multiple capability checks. Useful for seeing dense graphs.",
    filePath: "examples/v0.6/build/auto.quote.bind.issue.v2.l0.json",
    lawGoal: "branch-exclusive" as const,
  },
];

export default async function ExamplesPage() {
  const items = await fetchExamples();

  const quickCards = QUICK_EXAMPLES.map((example) => {
    const match = items.find((item) => item.l0Path === example.filePath);
    const detail = match
      ? { id: match.id, l0Path: match.l0Path }
      : undefined;
    return { ...example, detail };
  });

  const quickFilePaths = new Set(QUICK_EXAMPLES.map((example) => example.filePath));
  const remaining = items.filter((item) => !quickFilePaths.has(item.l0Path));

  return (
    <main className="px-6 md:px-10 py-10 space-y-10">
      <section className="space-y-3">
        <h1 className="text-2xl font-semibold tracking-tight">Explore pipeline samples</h1>
        <p className="text-sm text-zinc-300 max-w-2xl leading-relaxed">
          The cards below run Graph and Law checks directly from your browser, powered by the same
          in-repo APIs that back the detailed view. Use them for quick smoke tests, then hop into the
          detail screens for deeper dives.
        </p>
        <div className="grid gap-4 md:grid-cols-2">
          {quickCards.map((example) => (
            <ExampleCard key={example.filePath} {...example} />
          ))}
        </div>
      </section>

      <section className="space-y-3">
        <div className="flex items-center justify-between">
          <h2 className="text-xl font-semibold">All examples (v0.6)</h2>
          <span className="text-sm text-muted">Sourced from examples/v0.6/build</span>
        </div>
        <div className="grid md:grid-cols-2 lg:grid-cols-3 gap-4">
          {remaining.map((item) => (
            <Link
              key={item.id}
              href={`/examples/${encodeURIComponent(item.id)}?l0=${encodeURIComponent(item.l0Path)}`}
              className="card p-4 hover:outline outline-1 outline-white/10 transition"
            >
              <div className="text-lg font-medium">{item.title}</div>
              <div className="text-xs text-muted mt-1">{item.l0Path}</div>
            </Link>
          ))}
        </div>
        {items.length === 0 && (
          <div className="text-sm text-muted">
            No examples found under <code>examples/v0.6/build</code>.
          </div>
        )}
      </section>
    </main>
  );
}
