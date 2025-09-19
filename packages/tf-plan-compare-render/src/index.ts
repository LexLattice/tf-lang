import { CompareReport } from '@tf-lang/tf-plan-compare-core';
import { validateCompare } from '@tf-lang/tf-plan-core';

const TABLE_HEADER = '| Rank | Branch | Total | Risk | Notes |\n| --- | --- | --- | --- | --- |\n';

const HTML_STYLE = `body{font-family:system-ui,sans-serif;padding:1rem;background:#fdfdfd;color:#1a1a1a;}table{border-collapse:collapse;width:100%;margin-bottom:1.5rem;}th,td{border:1px solid #d0d0d0;padding:0.5rem;text-align:left;}th{background-color:#efefef;}h1{margin-top:0;}section{margin-bottom:1.5rem;}section h3{margin-bottom:0.5rem;}`;

const CSP_HEADER =
  "default-src 'none'; style-src 'self' 'unsafe-inline'; img-src 'self' data:; font-src 'self'; form-action 'none'; base-uri 'self'; frame-ancestors 'none';";

function escapeHtml(value: string): string {
  return value
    .replace(/&/g, '&amp;')
    .replace(/</g, '&lt;')
    .replace(/>/g, '&gt;')
    .replace(/"/g, '&quot;')
    .replace(/'/g, '&#39;');
}

function escapeMarkdownCell(value: string): string {
  const htmlEscaped = escapeHtml(value);
  return htmlEscaped.replace(/\|/g, '\\|').replace(/\n/g, ' ');
}

function safeNumber(value: number): string {
  if (!Number.isFinite(value)) {
    throw new Error(`Encountered non-finite number while rendering: ${value}`);
  }
  return value.toFixed(2);
}

function sanitizeHref(value: string | undefined): string | null {
  if (!value) {
    return null;
  }
  const trimmed = value.trim();
  if (trimmed.length === 0) {
    return null;
  }
  if (/^(https?:\/\/|\.\.?\/|\/)/iu.test(trimmed)) {
    return trimmed;
  }
  return null;
}

export function renderMarkdown(report: CompareReport): string {
  validateCompare(report);
  const header = `# tf-plan comparison (version ${escapeMarkdownCell(report.version)})\n\n`;
  const metaLines = [`*Seed:* ${escapeMarkdownCell(String(report.meta.seed))}`, `*Spec Hash:* ${escapeMarkdownCell(report.meta.specHash)}`];
  const tableRows = report.branches
    .map((branch) =>
      `| ${branch.rank} | ${escapeMarkdownCell(branch.branchName)} | ${escapeMarkdownCell(safeNumber(branch.score.total))} | ${escapeMarkdownCell(safeNumber(branch.score.risk))} | ${escapeMarkdownCell(branch.summary)} |`,
    )
    .join('\n');
  const oracleSection = report.branches
    .map((branch) => {
      const headerLine = `### ${escapeMarkdownCell(branch.branchName)}`;
      if (branch.oracles.length === 0) {
        return `${headerLine}\n- No oracle results available\n`;
      }
      const oracleLines = branch.oracles
        .map((oracle) => {
          const base = `- ${escapeMarkdownCell(oracle.name)}: ${escapeMarkdownCell(oracle.status)}`;
          const sanitizedHref = sanitizeHref(oracle.artifact);
          if (!sanitizedHref) {
            return base;
          }
          return `${base} ([artifact](${escapeMarkdownCell(sanitizedHref)}))`;
        })
        .join('\n');
      return `${headerLine}\n${oracleLines}\n`;
    })
    .join('\n');
  return `${header}${metaLines.join(' ')}\n\n${TABLE_HEADER}${tableRows}\n\n${oracleSection}`;
}

export function renderHtml(report: CompareReport): string {
  validateCompare(report);
  const rows = report.branches
    .map((branch) => {
      const branchName = escapeHtml(branch.branchName);
      const summary = escapeHtml(branch.summary);
      const total = escapeHtml(safeNumber(branch.score.total));
      const risk = escapeHtml(safeNumber(branch.score.risk));
      return `<tr><td>${branch.rank}</td><td>${branchName}</td><td>${total}</td><td>${risk}</td><td>${summary}</td></tr>`;
    })
    .join('');
  const oracleBlocks = report.branches
    .map((branch) => {
      if (branch.oracles.length === 0) {
        return `<section><h3>${escapeHtml(branch.branchName)}</h3><ul><li>No oracle results available</li></ul></section>`;
      }
      const items = branch.oracles
        .map((oracle) => {
          const name = escapeHtml(oracle.name);
          const status = escapeHtml(oracle.status);
          const details = oracle.details ? ` — ${escapeHtml(oracle.details)}` : '';
          const href = sanitizeHref(oracle.artifact);
          const artifactLink = href
            ? ` (<a rel="noopener noreferrer" target="_blank" href="${escapeHtml(href)}">artifact</a>)`
            : '';
          return `<li><strong>${name}</strong>: ${status}${details}${artifactLink}</li>`;
        })
        .join('');
      return `<section><h3>${escapeHtml(branch.branchName)}</h3><ul>${items}</ul></section>`;
    })
    .join('');
  return `<!doctype html><html lang="en"><head><meta charset="utf-8" /><title>tf-plan comparison</title><meta http-equiv="Content-Security-Policy" content="${CSP_HEADER}"><style>${HTML_STYLE}</style></head><body><h1>tf-plan comparison (version ${escapeHtml(report.version)})</h1><p><strong>Seed:</strong> ${escapeHtml(String(report.meta.seed))} · <strong>Spec Hash:</strong> ${escapeHtml(report.meta.specHash)}</p><table aria-describedby="summary"><thead><tr><th scope="col">Rank</th><th scope="col">Branch</th><th scope="col">Total</th><th scope="col">Risk</th><th scope="col">Summary</th></tr></thead><tbody>${rows}</tbody></table><div id="summary">${oracleBlocks}</div></body></html>`;
}
