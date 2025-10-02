"use client";

import { useEffect, useState } from "react";

import { apiLaws } from "../lib/tools";

type LawPanelProps = {
  filePath: string;
};

type LawResponse = {
  status: string;
  laws?: { branch_exclusive?: { results?: Array<{ branch?: string; guardVar?: string; status?: string; reason?: string }> } };
  counterexample?: unknown;
};

export default function LawPanel({ filePath }: LawPanelProps) {
  const [data, setData] = useState<LawResponse | null>(null);
  const [error, setError] = useState<string>("");

  useEffect(() => {
    let cancelled = false;
    setData(null);
    setError("");
    apiLaws({ filePath, goal: "branch-exclusive", maxBools: 6 })
      .then((response) => {
        if (!cancelled) setData(response);
      })
      .catch((err: unknown) => {
        if (!cancelled) setError(err instanceof Error ? err.message : String(err));
      });
    return () => {
      cancelled = true;
    };
  }, [filePath]);

  if (error) {
    return <div className="card p-4 text-red-400">{error}</div>;
  }
  if (!data) {
    return <div className="card p-4">Loading…</div>;
  }

  const statusClass =
    data.status === "GREEN" ? "badge-pass" : data.status === "RED" ? "badge-fail" : "badge-warn";
  const branchResults = data.laws?.branch_exclusive?.results ?? [];

  const counterexampleValue = data?.counterexample;
  const counterexampleString = counterexampleValue === undefined
    ? null
    : JSON.stringify(counterexampleValue, null, 2);

  return (
    <div className="card p-4 space-y-2">
      <div className="flex items-center gap-3">
        <div className="text-sm text-muted">Law checks:</div>
        <div className={`badge ${statusClass}`}>{data.status}</div>
      </div>
      <div className="text-sm text-muted mt-2">Branch exclusivity:</div>
      {branchResults.length === 0 ? (
        <div className="text-sm">No branches.</div>
      ) : (
        <ul className="text-sm space-y-1">
          {branchResults.map((entry, index) => (
            <li key={index}>
              • <span className="text-muted">{entry.branch || entry.guardVar || "(branch)"}:</span> {entry.status}
              {entry.reason ? ` — ${entry.reason}` : ""}
            </li>
          ))}
        </ul>
      )}
      {counterexampleString && (
        <div className="mt-3 space-y-1">
          <div className="text-sm text-muted">Counterexample (bounded):</div>
          <pre className="overflow-auto"><code>{counterexampleString}</code></pre>
        </div>
      )}
    </div>
  );
}
