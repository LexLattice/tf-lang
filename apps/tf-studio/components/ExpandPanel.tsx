"use client";

import { useState } from "react";

import CodeEditor from "./CodeEditor";
import { apiExpand } from "../lib/tools";

type ExpandPanelProps = {
  initialYaml?: string;
};

export default function ExpandPanel({ initialYaml = "" }: ExpandPanelProps) {
  const [yaml, setYaml] = useState<string>(initialYaml);
  const [result, setResult] = useState<unknown>(null);
  const [error, setError] = useState<string>("");
  const [isRunning, setIsRunning] = useState(false);

  async function runExpand() {
    try {
      setIsRunning(true);
      setError("");
      setResult(null);
      const response = await apiExpand(yaml);
      setResult(response.l0);
    } catch (err: unknown) {
      setError(err instanceof Error ? err.message : String(err));
    } finally {
      setIsRunning(false);
    }
  }

  return (
    <section className="space-y-4">
      <h2 className="text-xl font-semibold">Expand L2 → L0</h2>
      <CodeEditor initial={yaml} onChange={setYaml} />
      <button
        className="badge chip-transform"
        onClick={runExpand}
        disabled={isRunning}
      >
        {isRunning ? "Expanding…" : "Expand"}
      </button>
      {error && <div className="card p-3 text-red-400">{error}</div>}
      {result && (
        <div className="grid lg:grid-cols-2 gap-4">
          <div className="card p-3 space-y-2">
            <div className="text-sm text-muted">Expanded L0 (preview):</div>
            <pre className="overflow-auto text-xs"><code>{JSON.stringify(result, null, 2)}</code></pre>
          </div>
          <div className="card p-3 space-y-2">
            <div className="text-sm text-muted">Next steps:</div>
            <ul className="list-disc ml-4 text-sm space-y-1">
              <li>Save this L0 to <code>examples/v0.6/build/</code> and open in <code>/examples</code> for Graph/Effects/Typecheck/Laws.</li>
              <li>Or adapt the API to emit in-memory summaries for quick iteration.</li>
            </ul>
          </div>
        </div>
      )}
    </section>
  );
}
