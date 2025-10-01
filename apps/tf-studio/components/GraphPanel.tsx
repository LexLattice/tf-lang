"use client";

import { useEffect, useState } from "react";

import { apiGraph } from "../lib/tools";

type GraphPanelProps = {
  filePath: string;
};

export default function GraphPanel({ filePath }: GraphPanelProps) {
  const [dot, setDot] = useState<string>("");
  const [error, setError] = useState<string>("");

  useEffect(() => {
    let cancelled = false;
    setDot("");
    setError("");
    apiGraph(filePath)
      .then((response) => {
        if (!cancelled) setDot(response.dot ?? "");
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
    <div className="card p-4">
      <div className="text-sm text-muted mb-2">Graphviz DOT (copyable):</div>
      <pre className="overflow-auto"><code>{dot || "(loading…)"}</code></pre>
    </div>
  );
}
