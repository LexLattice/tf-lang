'use client';

import { useEffect, useMemo, useRef, useState } from "react";
import {
  ChevronRight,
  Download,
  GitBranch,
  Link as LinkIcon,
  Search,
  Upload,
} from "lucide-react";

// ---- Types -----------------------------------------------------------------
export type CapabilityKind =
  | "table"
  | "hypertable"
  | "enum"
  | "function"
  | "ca"
  | "mv"
  | "rule"
  | "endpoint"
  | "websocket"
  | "dag"
  | "migration"
  | "test"
  | "script"
  | "model"
  | "config";

export type CapabilityLayer = "ontology" | "logic" | "epistemology" | "methodology";

export interface CapabilityNode {
  id: string;
  name: string;
  layer: CapabilityLayer;
  kind: CapabilityKind;
  path?: string;
  provides?: string[];
  depends?: string[];
  links?: { label: string; url: string }[];
}

export interface CapabilitiesDoc {
  meta: {
    repo: string;
    generated_at: string;
    generator: string;
    commit?: string;
  };
  layers: Record<CapabilityLayer, { count: number }>;
  nodes: CapabilityNode[];
}

// ---- Utilities --------------------------------------------------------------
function groupBy<T, K extends string | number | symbol>(arr: T[], key: (item: T) => K): Record<K, T[]> {
  return arr.reduce((acc, item) => {
    const bucket = key(item);
    (acc[bucket] ||= [] as T[]).push(item);
    return acc;
  }, {} as Record<K, T[]>);
}

function cn(...parts: Array<string | false | null | undefined>): string {
  return parts.filter(Boolean).join(" ");
}

const LAYER_LABEL: Record<CapabilityLayer, string> = {
  ontology: "Ontology",
  logic: "Logic",
  epistemology: "Epistemology",
  methodology: "Methodology",
};

const KIND_BADGE: Record<CapabilityKind, string> = {
  table: "bg-blue-500/10 text-blue-200 border border-blue-400/30",
  hypertable: "bg-blue-500/10 text-blue-200 border border-blue-400/30",
  enum: "bg-blue-500/10 text-blue-200 border border-blue-400/30",
  function: "bg-violet-500/10 text-violet-200 border border-violet-400/30",
  ca: "bg-amber-500/10 text-amber-200 border border-amber-400/30",
  mv: "bg-amber-500/10 text-amber-200 border border-amber-400/30",
  rule: "bg-emerald-500/10 text-emerald-200 border border-emerald-400/30",
  endpoint: "bg-fuchsia-500/10 text-fuchsia-200 border border-fuchsia-400/30",
  websocket: "bg-fuchsia-500/10 text-fuchsia-200 border border-fuchsia-400/30",
  dag: "bg-slate-500/10 text-slate-200 border border-slate-400/30",
  migration: "bg-slate-500/10 text-slate-200 border border-slate-400/30",
  test: "bg-slate-500/10 text-slate-200 border border-slate-400/30",
  script: "bg-slate-500/10 text-slate-200 border border-slate-400/30",
  model: "bg-fuchsia-500/10 text-fuchsia-200 border border-fuchsia-400/30",
  config: "bg-slate-500/10 text-slate-200 border border-slate-400/30",
};

const LAYERS: Array<CapabilityLayer | "all"> = ["all", "ontology", "logic", "epistemology", "methodology"];

function LayerPill({ layer }: { layer: CapabilityLayer }) {
  const background =
    layer === "ontology"
      ? "bg-blue-600"
      : layer === "logic"
      ? "bg-violet-600"
      : layer === "epistemology"
      ? "bg-fuchsia-600"
      : "bg-slate-600";
  return (
    <span className={cn("inline-flex items-center rounded-full px-2 py-0.5 text-xs font-semibold uppercase tracking-wide text-white", background)}>
      {LAYER_LABEL[layer]}
    </span>
  );
}

function ToolbarButton(
  props: React.ButtonHTMLAttributes<HTMLButtonElement> & { variant?: "default" | "outline" | "ghost"; compact?: boolean },
) {
  const { className, variant = "default", compact = false, ...rest } = props;
  const base = "inline-flex items-center justify-center gap-2 rounded-lg font-medium transition focus:outline-none focus-visible:ring-2 focus-visible:ring-white/40";
  const sizing = compact ? "px-2.5 py-1.5 text-xs" : "px-3.5 py-2 text-sm";
  const palette =
    variant === "outline"
      ? "border border-white/15 bg-transparent hover:bg-white/10 text-[rgb(var(--text))]"
      : variant === "ghost"
      ? "bg-white/5 hover:bg-white/10 text-[rgb(var(--text))]"
      : "bg-white text-slate-900 hover:bg-slate-200";
  return <button className={cn(base, sizing, palette, className)} type="button" {...rest} />;
}

function FilterChip({ active, children, onClick }: { active: boolean; children: React.ReactNode; onClick: () => void }) {
  return (
    <button
      type="button"
      onClick={onClick}
      className={cn(
        "rounded-full border px-3 py-1 text-xs font-semibold transition",
        active ? "bg-white text-slate-900 border-white" : "border-white/20 bg-white/5 text-[rgb(var(--text))]/80 hover:bg-white/10",
      )}
    >
      {children}
    </button>
  );
}

// ---- Page -------------------------------------------------------------------
export default function CapabilitiesPage() {
  const [doc, setDoc] = useState<CapabilitiesDoc | null>(null);
  const [query, setQuery] = useState("");
  const [activeLayer, setActiveLayer] = useState<CapabilityLayer | "all">("all");
  const [selected, setSelected] = useState<CapabilityNode | null>(null);
  const fileInputRef = useRef<HTMLInputElement | null>(null);

  useEffect(() => {
    let cancelled = false;
    (async () => {
      try {
        const response = await fetch("/capabilities.json");
        if (!response.ok) return;
        const payload: CapabilitiesDoc = await response.json();
        if (!cancelled) {
          setDoc(payload);
          setSelected(null);
        }
      } catch {
        // ignore network/file errors — manual upload is available
      }
    })();
    return () => {
      cancelled = true;
    };
  }, []);

  const nodes = doc?.nodes ?? [];

  const filtered = useMemo(() => {
    const trimmed = query.trim().toLowerCase();
    const scoped = activeLayer === "all" ? nodes : nodes.filter((node) => node.layer === activeLayer);
    if (!trimmed) return scoped;
    return scoped.filter((node) => {
      const haystack = [node.name, node.id, node.path ?? ""].join(" ").toLowerCase();
      if (haystack.includes(trimmed)) return true;
      return (node.provides ?? []).some((entry) => entry.toLowerCase().includes(trimmed));
    });
  }, [nodes, query, activeLayer]);

  const byLayer = useMemo(() => groupBy(filtered, (node) => node.layer), [filtered]);

  const kindStats = useMemo(() => {
    const byKind = groupBy(filtered, (node) => node.kind);
    return Object.entries(byKind)
      .map(([kind, entries]) => ({ kind: kind as CapabilityKind, count: entries.length }))
      .sort((a, b) => b.count - a.count);
  }, [filtered]);

  const datasetMeta = useMemo(() => {
    if (!doc) return null;
    const total = doc.nodes.length;
    const generated = doc.meta.generated_at ? new Date(doc.meta.generated_at) : null;
    return {
      total,
      repo: doc.meta.repo,
      generatedAt: generated ? generated.toLocaleString() : doc.meta.generated_at,
      generator: doc.meta.generator,
      commit: doc.meta.commit,
    };
  }, [doc]);

  function handleUpload(event: React.ChangeEvent<HTMLInputElement>) {
    const file = event.target.files?.[0];
    if (!file) return;
    const reader = new FileReader();
    reader.onload = () => {
      try {
        const parsed = JSON.parse(String(reader.result));
        setDoc(parsed);
        setSelected(null);
      } catch {
        // eslint-disable-next-line no-alert
        alert("Invalid capabilities JSON file.");
      }
    };
    reader.readAsText(file);
    event.target.value = "";
  }

  function exportSelection() {
    if (!doc || filtered.length === 0) return;
    const subset: CapabilitiesDoc = { ...doc, nodes: filtered };
    const blob = new Blob([`${JSON.stringify(subset, null, 2)}\n`], { type: "application/json" });
    const url = URL.createObjectURL(blob);
    const anchor = document.createElement("a");
    anchor.href = url;
    anchor.download = "capabilities.filtered.json";
    anchor.click();
    URL.revokeObjectURL(url);
  }

  return (
    <main className="px-6 md:px-10 py-8 space-y-6">
      <header className="flex flex-wrap items-center justify-between gap-2">
        <div className="flex items-center gap-2 text-lg font-semibold tracking-tight">
          <GitBranch className="h-5 w-5" /> Capabilities Explorer
        </div>
        {datasetMeta && (
          <div className="text-xs text-muted">
            {datasetMeta.total} nodes · generated by {datasetMeta.generator}
            {datasetMeta.generatedAt ? ` on ${datasetMeta.generatedAt}` : ""}
          </div>
        )}
      </header>

      <div className="grid gap-4 lg:grid-cols-[minmax(0,2fr)_minmax(0,1fr)]">
        <section className="space-y-4">
          <div className="card p-5 space-y-3">
            <div className="flex flex-wrap items-center gap-2">
              <div className="relative flex-1 min-w-[220px]">
                <Search className="pointer-events-none absolute left-3 top-1/2 h-4 w-4 -translate-y-1/2 text-muted" />
                <input
                  value={query}
                  onChange={(event) => setQuery(event.target.value)}
                  placeholder="Search by name, id, path, or contract…"
                  className="h-10 w-full rounded-lg border border-white/10 bg-white/5 pl-9 pr-3 text-sm outline-none transition focus:border-white/30"
                  type="search"
                />
              </div>
              <input ref={fileInputRef} type="file" accept="application/json" className="hidden" onChange={handleUpload} />
              <ToolbarButton variant="outline" onClick={() => fileInputRef.current?.click()}>
                <Upload className="h-4 w-4" /> Load JSON
              </ToolbarButton>
              <ToolbarButton onClick={exportSelection} disabled={!doc || filtered.length === 0} className={cn(!doc || filtered.length === 0 ? "cursor-not-allowed opacity-60" : "")}>
                <Download className="h-4 w-4" /> Export
              </ToolbarButton>
            </div>
            <div className="flex flex-wrap gap-2">
              {LAYERS.map((layer) => (
                <FilterChip key={layer} active={activeLayer === layer} onClick={() => setActiveLayer(layer as CapabilityLayer | "all")}>
                  {layer === "all" ? "All layers" : LAYER_LABEL[layer as CapabilityLayer]}
                </FilterChip>
              ))}
            </div>
          </div>

          <div className="card p-5 space-y-3">
            <div className="text-sm font-semibold">Kinds in view</div>
            <div className="flex flex-wrap gap-2">
              {kindStats.length === 0 && <span className="text-xs text-muted">No capabilities loaded yet.</span>}
              {kindStats.map((entry) => (
                <span key={entry.kind} className={cn("inline-flex items-center gap-1 rounded-full px-2.5 py-1 text-[11px] uppercase tracking-wide", KIND_BADGE[entry.kind])}>
                  {entry.kind} · {entry.count}
                </span>
              ))}
            </div>
          </div>

          {(["ontology", "logic", "epistemology", "methodology"] as CapabilityLayer[]).map((layer) => {
            const entries = (byLayer[layer] ?? []).slice().sort((a, b) => a.name.localeCompare(b.name));
            return (
              <div key={layer} className="card p-5 space-y-3">
                <div className="flex items-center justify-between">
                  <div className="flex items-center gap-2">
                    <LayerPill layer={layer} />
                    <span className="text-xs text-muted">{entries.length} items</span>
                  </div>
                </div>
                <div className="max-h-72 overflow-y-auto pr-1">
                  {entries.length === 0 ? (
                    <div className="text-xs text-muted">No entries in view.</div>
                  ) : (
                    <ul className="space-y-1">
                      {entries.map((node) => (
                        <li key={node.id}>
                          <button
                            type="button"
                            onClick={() => setSelected(node)}
                            className={cn(
                              "flex w-full items-center gap-2 rounded-lg px-2 py-1.5 text-left transition hover:bg-white/5",
                              selected?.id === node.id ? "bg-white/10" : "",
                            )}
                          >
                            <ChevronRight className="h-4 w-4 text-muted" />
                            <span className="font-medium">{node.name}</span>
                            <span className={cn("ml-2 rounded border px-2 py-0.5 text-[10px] capitalize", KIND_BADGE[node.kind])}>{node.kind}</span>
                            {node.path && <span className="ml-auto truncate text-[11px] text-muted">{node.path}</span>}
                          </button>
                        </li>
                      ))}
                    </ul>
                  )}
                </div>
              </div>
            );
          })}
        </section>

        <aside className="space-y-4">
          <div className="card sticky top-6 p-5 space-y-3">
            <div className="text-lg font-semibold">{selected ? selected.name : "Select a capability"}</div>
            {selected ? (
              <div className="space-y-3 text-sm">
                <div className="flex flex-wrap items-center gap-2">
                  <LayerPill layer={selected.layer} />
                  <span className={cn("rounded border px-2 py-0.5 text-[11px] capitalize", KIND_BADGE[selected.kind])}>{selected.kind}</span>
                  <span className="text-xs text-muted">id: {selected.id}</span>
                </div>
                {selected.path && (
                  <div className="space-y-1">
                    <div className="text-xs text-muted uppercase">Path</div>
                    <div className="font-mono text-xs text-white/90">{selected.path}</div>
                  </div>
                )}
                {selected.provides && selected.provides.length > 0 && (
                  <div className="space-y-1">
                    <div className="text-xs text-muted uppercase">Contracts</div>
                    <div className="flex flex-wrap gap-1">
                      {selected.provides.map((contract) => (
                        <span key={contract} className="rounded border border-white/15 bg-white/5 px-2 py-0.5 font-mono text-[10px]">
                          {contract}
                        </span>
                      ))}
                    </div>
                  </div>
                )}
                {selected.depends && selected.depends.length > 0 && (
                  <div className="space-y-1">
                    <div className="text-xs text-muted uppercase">Depends on</div>
                    <div className="flex flex-wrap gap-1">
                      {selected.depends.map((dep) => (
                        <span key={dep} className="rounded border border-white/15 bg-white/5 px-2 py-0.5 font-mono text-[10px]">
                          {dep}
                        </span>
                      ))}
                    </div>
                  </div>
                )}
                {selected.links && selected.links.length > 0 && (
                  <div className="space-y-1">
                    <div className="text-xs text-muted uppercase">Links</div>
                    <ul className="space-y-1">
                      {selected.links.map((link) => (
                        <li key={`${link.label}-${link.url}`} className="flex items-center gap-2 text-sm">
                          <LinkIcon className="h-4 w-4" />
                          <a className="underline" href={link.url} target="_blank" rel="noreferrer">
                            {link.label}
                          </a>
                        </li>
                      ))}
                    </ul>
                  </div>
                )}
              </div>
            ) : (
              <p className="text-sm text-muted">Choose an item from the list to see its contracts, dependencies, and asset links.</p>
            )}
          </div>

          <div className="card p-5 space-y-2 text-sm text-muted">
            <div className="text-sm font-semibold text-[rgb(var(--text))]">How to use</div>
            <div>
              <div className="font-semibold text-[rgb(var(--text))]">Load data</div>
              Place <code>capabilities.json</code> in the app&apos;s <code>public/</code> directory (or click <em>Load JSON</em> to upload the latest file from <code>docs/capabilities/</code>).
            </div>
            <div>
              <div className="font-semibold text-[rgb(var(--text))]">Filter & export</div>
              Narrow results with search and layer filters, then click <em>Export</em> to save a filtered capabilities bundle.
            </div>
          </div>

          {datasetMeta && (
            <div className="card p-5 space-y-2 text-sm">
              <div className="text-sm font-semibold">Dataset</div>
              <div className="flex flex-col gap-1 text-muted">
                <span>Repository: {datasetMeta.repo}</span>
                {datasetMeta.commit && <span>Commit: {datasetMeta.commit}</span>}
                {datasetMeta.generatedAt && <span>Generated: {datasetMeta.generatedAt}</span>}
                <span>Total nodes: {datasetMeta.total.toLocaleString()}</span>
              </div>
            </div>
          )}
        </aside>
      </div>
    </main>
  );
}
