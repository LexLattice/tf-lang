"use client";

import { useEffect, useState } from "react";

import { apiEffects } from "../lib/tools";

type EffectsPanelProps = {
  filePath: string;
};

export default function EffectsPanel({ filePath }: EffectsPanelProps) {
  const [summary, setSummary] = useState<string>("");
  const [error, setError] = useState<string>("");

  useEffect(() => {
    let cancelled = false;
    setSummary("");
    setError("");
    apiEffects(filePath)
      .then((response) => {
        if (!cancelled) setSummary(response.summary ?? "");
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

  return (
    <div className="card p-4 flex items-center gap-3">
      <div className="text-sm text-muted">Effects:</div>
      <div className="badge">{summary || "…"}</div>
    </div>
  );
}
