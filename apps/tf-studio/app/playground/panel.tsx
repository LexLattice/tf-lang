"use client";

import { FormEvent, useState } from "react";
import { apiGraph, apiLaws } from "../../lib/tools";

type PlaygroundState = {
  graph?: string;
  laws?: object;
  error?: string;
  busy: boolean;
};

export default function PlaygroundPanel() {
  const [filePath, setFilePath] = useState("examples/v0.6/build/auto.fnol.fasttrack.v1.l0.json");
  const [goal, setGoal] = useState<"branch-exclusive">("branch-exclusive");
  const [state, setState] = useState<PlaygroundState>({ busy: false });

  async function runGraph(e: FormEvent) {
    e.preventDefault();
    setState({ busy: true });
    try {
      const result = await apiGraph(filePath);
      setState({ busy: false, graph: result.dot });
    } catch (err) {
      setState({ busy: false, error: err instanceof Error ? err.message : String(err) });
    }
  }

  async function runLaws(e: FormEvent) {
    e.preventDefault();
    setState({ busy: true });
    try {
      const result = await apiLaws({ filePath, goal });
      setState({ busy: false, laws: result });
    } catch (err) {
      setState({ busy: false, error: err instanceof Error ? err.message : String(err) });
    }
  }

  return (
    <section className="card p-6 space-y-4">
      <form className="space-y-3" onSubmit={runGraph}>
        <label className="block text-sm font-medium text-zinc-300">
          File path
          <input
            className="mt-1 w-full rounded-md bg-black/40 border border-white/10 px-3 py-2 text-sm focus:outline-none focus:ring-2 focus:ring-tf-transform/50"
            value={filePath}
            onChange={(event) => setFilePath(event.target.value)}
            placeholder="examples/..."
          />
        </label>

        <label className="block text-sm font-medium text-zinc-300">
          Law goal
          <select
            className="mt-1 w-full rounded-md bg-black/40 border border-white/10 px-3 py-2 text-sm focus:outline-none focus:ring-2 focus:ring-tf-publish/50"
            value={goal}
            onChange={(event) => setGoal(event.target.value as typeof goal)}
          >
            <option value="branch-exclusive">branch-exclusive</option>
          </select>
        </label>

        <div className="flex flex-wrap gap-2 pt-2">
          <button
            type="submit"
            disabled={state.busy}
            className="badge chip-transform border-white/10"
          >
            {state.busy ? "Running…" : "Build graph"}
          </button>
          <button
            type="button"
            disabled={state.busy}
            onClick={runLaws}
            className="badge chip-publish border-white/10"
          >
            {state.busy ? "Running…" : "Check laws"}
          </button>
        </div>
      </form>

      {state.error && <div className="text-xs text-red-400">{state.error}</div>}
      {state.graph && (
        <div className="space-y-2">
          <div className="text-xs uppercase tracking-wide text-zinc-500">Graph (DOT)</div>
          <pre className="text-xs max-h-56 overflow-auto bg-black/40 p-3 rounded">{state.graph}</pre>
        </div>
      )}
      {state.laws && (
        <div className="space-y-2">
          <div className="text-xs uppercase tracking-wide text-zinc-500">Laws result</div>
          <pre className="text-xs max-h-56 overflow-auto bg-black/40 p-3 rounded">
            {JSON.stringify(state.laws, null, 2)}
          </pre>
        </div>
      )}
    </section>
  );
}
