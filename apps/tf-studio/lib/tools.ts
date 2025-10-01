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

export async function apiEffects(filePath: string) {
  const r = await fetch("/api/cli/effects", {
    method: "POST",
    headers: { "content-type": "application/json" },
    body: JSON.stringify({ filePath }),
  });
  if (!r.ok) throw new Error(await r.text());
  return r.json() as Promise<{ summary: string }>;
}

export async function apiTypecheck(filePath: string, adaptersPath?: string) {
  const r = await fetch("/api/cli/typecheck", {
    method: "POST",
    headers: { "content-type": "application/json" },
    body: JSON.stringify({ filePath, adaptersPath }),
  });
  if (!r.ok) throw new Error(await r.text());
  return r.json();
}

export async function apiPlanInstances(opts: {
  filePath: string;
  groupBy?: "domain" | "scheme";
  registryPath?: string;
}) {
  const r = await fetch("/api/cli/plan-instances", {
    method: "POST",
    headers: { "content-type": "application/json" },
    body: JSON.stringify(opts),
  });
  if (!r.ok) throw new Error(await r.text());
  return r.json();
}

export async function apiExpand(l2Yaml: string) {
  const r = await fetch("/api/cli/expand", {
    method: "POST",
    headers: { "content-type": "application/json" },
    body: JSON.stringify({ l2Yaml }),
  });
  if (!r.ok) throw new Error(await r.text());
  return r.json() as Promise<{ l0: unknown }>;
}
