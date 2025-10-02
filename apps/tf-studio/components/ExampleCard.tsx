"use client";

import Link from "next/link";
import { useState } from "react";

import { apiGraph, apiLaws } from "../lib/tools";

type DetailLink = {
  id: string;
  l0Path: string;
};

type ExampleCardProps = {
  title: string;
  description?: string;
  filePath: string;
  detail?: DetailLink;
  lawGoal?: "branch-exclusive";
};

type BusyState = "graph" | "laws" | null;

export default function ExampleCard({ title, description, filePath, detail, lawGoal }: ExampleCardProps) {
  const [busy, setBusy] = useState<BusyState>(null);
  const [error, setError] = useState<string | null>(null);
  const [graph, setGraph] = useState<string | null>(null);
  const [lawResult, setLawResult] = useState<object | null>(null);

  async function handleGraph() {
    setBusy("graph");
    setError(null);
    setLawResult(null);
    try {
      const res = await apiGraph(filePath);
      setGraph(res.dot);
    } catch (err) {
      setGraph(null);
      setError(err instanceof Error ? err.message : String(err));
    } finally {
      setBusy(null);
    }
  }

  async function handleLaws() {
    if (!lawGoal) return;
    setBusy("laws");
    setError(null);
    setGraph(null);
    try {
      const res = await apiLaws({ filePath, goal: lawGoal });
      setLawResult(res);
    } catch (err) {
      setLawResult(null);
      setError(err instanceof Error ? err.message : String(err));
    } finally {
      setBusy(null);
    }
  }

  return (
    <article className="card p-5 space-y-3">
      <div className="space-y-1">
        <h2 className="text-lg font-medium">{title}</h2>
        {description && <p className="text-sm text-zinc-400 leading-relaxed">{description}</p>}
      </div>

      <div className="text-xs text-zinc-500">
        File: <code>{filePath}</code>
        {detail && (
          <Link
            href={{
              pathname: "/examples/[id]",
              query: { id: detail.id, l0: detail.l0Path },
            }}
            className="badge chip-keypair border-white/10"
          >
            Open detail
          </Link>
        )}
      </div>

      <div className="flex flex-wrap gap-2 pt-2">
        <button
          type="button"
          onClick={handleGraph}
          disabled={busy !== null}
          className="badge chip-transform border-white/10"
        >
          {busy === "graph" ? "Loading graph…" : "View graph"}
        </button>
        {lawGoal && (
          <button
            type="button"
            onClick={handleLaws}
            disabled={busy !== null}
            className="badge chip-publish border-white/10"
          >
            {busy === "laws" ? "Checking laws…" : "Run laws"}
          </button>
        )}
      </div>

      {error && <div className="text-xs text-red-400">{error}</div>}

      {graph && (
        <div className="space-y-2">
          <div className="text-xs uppercase tracking-wide text-zinc-500">Graph (DOT)</div>
          <pre className="text-xs max-h-52 overflow-auto bg-black/40 p-3 rounded">{graph}</pre>
        </div>
      )}

      {lawResult && (
        <div className="space-y-2">
          <div className="text-xs uppercase tracking-wide text-zinc-500">Laws result</div>
          <pre className="text-xs max-h-52 overflow-auto bg-black/40 p-3 rounded">
            {JSON.stringify(lawResult, null, 2)}
          </pre>
        </div>
      )}
    </article>
  );
}
