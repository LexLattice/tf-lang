"use client";

import { useState } from "react";

import { apiLaws, apiPlanInstances, apiTypecheck } from "../lib/tools";

type Message = { role: "system" | "user" | "agent"; text: string };

type ChatDockProps = {
  filePath: string;
};

export default function ChatDock({ filePath }: ChatDockProps) {
  const [messages, setMessages] = useState<Message[]>([{
    role: "system",
    text: "Welcome to TF-Studio. Try a guided probe: Laws, Typecheck, or Instance Plan.",
  }]);

  async function run(kind: "laws" | "typecheck" | "plan") {
    setMessages((prev) => [...prev, { role: "user", text: `Run ${kind}` }]);
    try {
      if (kind === "laws") {
        const response = await apiLaws({ filePath, goal: "branch-exclusive", maxBools: 6 });
        setMessages((prev) => [
          ...prev,
          { role: "agent", text: `Laws status: ${response.status}.` },
        ]);
      } else if (kind === "typecheck") {
        const response = await apiTypecheck(filePath);
        const suggestions = Array.isArray(response?.suggestions)
          ? response.suggestions.length
          : Array.isArray(response?.mismatches)
            ? response.mismatches.length
            : 0;
        setMessages((prev) => [
          ...prev,
          { role: "agent", text: `Typecheck: ${response.status}. ${suggestions} suggestion(s).` },
        ]);
      } else {
        const response = await apiPlanInstances({ filePath, groupBy: "scheme" });
        const buckets = response?.schemes || response?.domains || response?.channels || {};
        setMessages((prev) => [
          ...prev,
          { role: "agent", text: `Instances by scheme: ${Object.keys(buckets).length} entries.` },
        ]);
      }
    } catch (error: unknown) {
      setMessages((prev) => [
        ...prev,
        { role: "agent", text: `Error: ${error instanceof Error ? error.message : String(error)}` },
      ]);
    }
  }

  return (
    <div className="card p-3 space-y-2">
      <div className="text-sm text-muted">Game Master</div>
      <div className="h-48 overflow-auto bg-black/20 rounded p-2">
        {messages.map((message, index) => (
          <div key={index} className="mb-1">
            <span className="text-muted">{message.role}: </span>
            {message.text}
          </div>
        ))}
      </div>
      <div className="flex gap-2">
        <button className="badge chip-keypair" onClick={() => run("laws")}>
          Laws
        </button>
        <button className="badge chip-transform" onClick={() => run("typecheck")}>
          Typecheck
        </button>
        <button className="badge chip-publish" onClick={() => run("plan")}>
          Plan by scheme
        </button>
      </div>
    </div>
  );
}
