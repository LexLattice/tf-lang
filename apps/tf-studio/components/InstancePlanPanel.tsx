"use client";

import { useEffect, useState } from "react";

import { apiPlanInstances } from "../lib/tools";

type InstancePlanPanelProps = {
  filePath: string;
};

type GroupByOption = "domain" | "scheme";

type PlanSummary = {
  domains?: Record<string, { total: number; instances: Record<string, number> }>;
  schemes?: Record<string, { total: number; instances: Record<string, number> }>;
  channels?: Record<string, { total: number; instances: Record<string, number> }>;
};

export default function InstancePlanPanel({ filePath }: InstancePlanPanelProps) {
  const [groupBy, setGroupBy] = useState<GroupByOption>("domain");
  const [data, setData] = useState<PlanSummary | null>(null);
  const [error, setError] = useState<string>("");

  useEffect(() => {
    let cancelled = false;
    setData(null);
    setError("");
    apiPlanInstances({ filePath, groupBy })
      .then((response) => {
        if (!cancelled) setData(response);
      })
      .catch((err: unknown) => {
        if (!cancelled) setError(err instanceof Error ? err.message : String(err));
      });
    return () => {
      cancelled = true;
    };
  }, [filePath, groupBy]);

  if (error) {
    return <div className="card p-4 text-red-400">{error}</div>;
  }
  if (!data) {
    return <div className="card p-4">Loading…</div>;
  }

  const buckets = groupBy === "domain" ? data.domains : data.schemes;

  return (
    <div className="card p-4 space-y-3">
      <div className="flex items-center justify-between">
        <div className="text-sm text-muted">Instance plan (group by {groupBy})</div>
        <div className="flex gap-2">
          <button className="badge" onClick={() => setGroupBy("domain")}>domain</button>
          <button className="badge" onClick={() => setGroupBy("scheme")}>scheme</button>
        </div>
      </div>
      <table className="w-full text-sm">
        <thead>
          <tr className="text-muted">
            <th className="text-left">Key</th>
            <th>Total</th>
            <th className="text-left">Instances</th>
          </tr>
        </thead>
        <tbody>
          {buckets &&
            Object.entries(buckets).map(([key, value]) => (
              <tr key={key} className="border-t border-white/10">
                <td>{key}</td>
                <td className="text-center">{value.total}</td>
                <td>
                  {Object.entries(value.instances)
                    .map(([instance, count]) => `${instance}×${count}`)
                    .join(", ")}
                </td>
              </tr>
            ))}
        </tbody>
      </table>
    </div>
  );
}
