"use client";

import { useEffect, useState } from "react";

import { apiTypecheck } from "../lib/tools";

type TypecheckPanelProps = {
  filePath: string;
};

type TypecheckReport = {
  status: string;
  suggestions?: Array<any>;
  mismatches?: Array<any>;
  describe?: (value: unknown) => string;
};

export default function TypecheckPanel({ filePath }: TypecheckPanelProps) {
  const [report, setReport] = useState<TypecheckReport | null>(null);
  const [error, setError] = useState<string>("");

  useEffect(() => {
    let cancelled = false;
    setReport(null);
    setError("");
    apiTypecheck(filePath)
      .then((response) => {
        if (!cancelled) setReport(response);
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
  if (!report) {
    return <div className="card p-4">Loading…</div>;
  }

  const statusClass =
    report.status === "ok" ? "badge-pass" : report.status === "needs-adapter" ? "badge-warn" : "badge-fail";
  const rows = report.suggestions ?? report.mismatches ?? [];

  return (
    <div className="card p-4 space-y-2">
      <div className="text-sm text-muted">Typecheck:</div>
      <div className={`badge ${statusClass}`}>{report.status}</div>
      {rows.length > 0 && (
        <table className="w-full text-sm mt-2">
          <thead>
            <tr className="text-muted">
              <th className="text-left">Port</th>
              <th className="text-left">From</th>
              <th>→</th>
              <th className="text-left">To</th>
              <th className="text-left">Adapter</th>
            </tr>
          </thead>
          <tbody>
            {rows.map((row: any, index: number) => (
              <tr key={index} className="border-t border-white/10">
                <td>{row.port || row.portPath?.join(".") || "in"}</td>
                <td>{row.sourceVar}</td>
                <td>→</td>
                <td>{report.describe?.(row.expected) ?? JSON.stringify(row.expected)}</td>
                <td>{row.adapter?.op || "-"}</td>
              </tr>
            ))}
          </tbody>
        </table>
      )}
    </div>
  );
}
