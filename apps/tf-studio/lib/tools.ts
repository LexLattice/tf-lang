export async function apiGraph(filePath: string, strict = false) {
  const r = await fetch("/api/cli/graph", {
    method: "POST",
    headers: { "content-type": "application/json" },
    body: JSON.stringify({ filePath, strict }),
  });
  if (!r.ok) throw new Error(await r.text());
  return r.json() as Promise<{ dot: string; file: string }>;
}

export async function apiLaws(opts: {
  filePath: string; goal?: "branch-exclusive"; maxBools?: number; policyPath?: string; capsPath?: string;
}) {
  const r = await fetch("/api/cli/laws", {
    method: "POST",
    headers: { "content-type": "application/json" },
    body: JSON.stringify(opts),
  });
  if (!r.ok) throw new Error(await r.text());
  return r.json() as Promise<{
    status: "GREEN" | "RED";
    laws: any;
    counterexample?: any;
    file: string;
  }>;
}
