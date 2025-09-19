import { readFile } from "node:fs/promises";
import path from "node:path";
import { findRepoRoot } from "@tf-lang/utils";
import type { TemplateFileTemplate, TemplatePack } from "@tf-lang/tf-plan-scaffold-core";

interface RawFileEntry {
  readonly source: string;
  readonly target?: string;
  readonly targetTemplate?: string;
}

interface RawTemplateMetadata {
  readonly name?: string;
  readonly description?: string;
  readonly workdir?: { readonly files?: readonly RawFileEntry[] };
  readonly repo?: { readonly files?: readonly RawFileEntry[] };
  readonly ci?: {
    readonly reusableWorkflow?: RawFileEntry;
    readonly branchWorkflows?: readonly RawFileEntry[];
    readonly branchWorkflow?: RawFileEntry;
  };
  readonly packageJson?: {
    readonly scripts?: Record<string, string>;
  };
}

function isFileEntryArray(value: RawFileEntry | readonly RawFileEntry[]): value is readonly RawFileEntry[] {
  return Array.isArray(value);
}

function assertNonEmpty(value: string | undefined, label: string): string {
  if (!value || value.trim().length === 0) {
    throw new Error(`${label} must be a non-empty string`);
  }
  return value;
}

async function loadTemplateFile(
  root: string,
  entry: RawFileEntry,
  scope: "branch" | "global",
  target: "workdir" | "repo" | "ci"
): Promise<TemplateFileTemplate> {
  const source = assertNonEmpty(entry.source, "template source");
  const absolute = path.join(root, source);
  const content = await readFile(absolute, "utf-8");
  const targetPath = entry.target ?? entry.targetTemplate;
  const relativePathTemplate = assertNonEmpty(targetPath, "template target");
  return {
    scope,
    target,
    sourcePath: path.posix.normalize(source.replace(/\\/g, "/")),
    relativePathTemplate,
    contentTemplate: content,
  };
}

function normalizeWorkflowEntries(entry?: RawFileEntry | readonly RawFileEntry[]): RawFileEntry[] {
  if (!entry) {
    return [];
  }
  if (isFileEntryArray(entry)) {
    return [...entry];
  }
  return [entry];
}

export interface LoadTemplateOptions {
  readonly repoRoot?: string;
}

export async function loadTemplatePack(
  templateName: string,
  options: LoadTemplateOptions = {}
): Promise<TemplatePack> {
  const repoRoot = options.repoRoot ?? findRepoRoot();
  const templateRoot = path.join(repoRoot, "templates", "t4", templateName);
  const metadataPath = path.join(templateRoot, "template.json");
  const raw = await readFile(metadataPath, "utf-8");
  const metadata = JSON.parse(raw) as RawTemplateMetadata;

  const files: TemplateFileTemplate[] = [];

  const workdirEntries = metadata.workdir?.files ?? [];
  for (const entry of workdirEntries) {
    files.push(await loadTemplateFile(templateRoot, entry, "branch", "workdir"));
  }

  const repoEntries = metadata.repo?.files ?? [];
  for (const entry of repoEntries) {
    files.push(await loadTemplateFile(templateRoot, entry, "global", "repo"));
  }

  const reusable = metadata.ci?.reusableWorkflow;
  if (reusable) {
    files.push(await loadTemplateFile(templateRoot, reusable, "global", "ci"));
  }

  const branchWorkflows = [
    ...normalizeWorkflowEntries(metadata.ci?.branchWorkflow),
    ...normalizeWorkflowEntries(metadata.ci?.branchWorkflows),
  ];
  for (const entry of branchWorkflows) {
    files.push(await loadTemplateFile(templateRoot, entry, "branch", "ci"));
  }

  files.sort((a, b) => a.sourcePath.localeCompare(b.sourcePath));

  return {
    name: metadata.name ?? templateName,
    description: metadata.description ?? `${templateName} scaffold template`,
    files,
    packageJsonScripts: metadata.packageJson?.scripts ?? {},
  };
}
