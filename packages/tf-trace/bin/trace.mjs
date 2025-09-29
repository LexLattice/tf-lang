#!/usr/bin/env node
import { mkdir, readFile, writeFile } from 'node:fs/promises';
import { dirname, resolve } from 'node:path';

import { ingestTraceFile } from '../dist/lib/ingest.js';
import { summarizeTrace } from '../dist/lib/summary.js';
import { evaluateBudget } from '../dist/lib/budget.js';

const context = {
  quiet: false,
  summaryDecimals: parseSummaryDecimals(),
  failOnViolation: false,
  outputFormat: 'json',
  grepPattern: undefined
};

function parseSummaryDecimals() {
  const raw = process.env.TRACE_SUMMARY_DECIMALS;
  if (raw === undefined) return undefined;
  const value = Number.parseInt(raw, 10);
  if (!Number.isFinite(value) || value < 0) {
    return undefined;
  }
  return value;
}

function maybeRoundMs(value) {
  if (typeof value !== 'number') return value;
  const decimals = context.summaryDecimals;
  if (decimals === undefined) return value;
  const factor = 10 ** decimals;
  return Math.round(value * factor) / factor;
}

function parseGlobalOptions(argv) {
  const options = {
    quiet: false,
    json: true,
    help: false,
    format: 'json',
    failOnViolation: false,
    grep: undefined
  };
  const rest = [];
  for (let i = 0; i < argv.length; i++) {
    const arg = argv[i];
    if (arg === '--quiet') {
      options.quiet = true;
      continue;
    }
    if (arg === '--json') {
      options.json = true;
      continue;
    }
    if (arg === '--fail-on-violation') {
      options.failOnViolation = true;
      continue;
    }
    if (arg === '--format') {
      const value = argv[i + 1];
      if (value) {
        options.format = value;
        i += 1;
      }
      continue;
    }
    if (arg === '--grep') {
      const value = argv[i + 1];
      if (value) {
        options.grep = value;
        i += 1;
      } else {
        options.grep = '';
      }
      continue;
    }
    if (arg === '--help' || arg === '-h') {
      options.help = true;
      continue;
    }
    rest.push(arg);
  }
  return { options, rest };
}

function getOption(args, key) {
  const index = args.indexOf(key);
  if (index === -1) return undefined;
  return args[index + 1];
}

function normalizeStatus(status) {
  const { ok, ...rest } = status;
  const normalized = { ok: Boolean(ok) };
  for (const [key, value] of Object.entries(rest)) {
    normalized[key] = value;
  }
  return normalized;
}

function printStatus(status) {
  const normalized = normalizeStatus(status);
  process.stdout.write(`${JSON.stringify(normalized)}\n`);
}

function logDiagnostic(message, { force = false } = {}) {
  if (!force && context.quiet) return;
  process.stderr.write(`${message}\n`);
}

function printHelp() {
  const lines = [
    'tf-trace <command> [options]',
    '',
    'Commands:',
    '  validate --in <trace.jsonl>',
    '  summary  --in <trace.jsonl> --out <file>',
    '  budget   (--in <trace.jsonl> | --summary-in <file>) --budgets <file>',
    '  export   (--in <trace.jsonl> | --summary <file>) --csv <file>',
    '',
    'Options:',
    '  --in <trace.jsonl>          Trace input for validate/summary/budget/export',
    '  --budgets <file>            Budget specification JSON (alias: --spec)',
    '  --grep <re>                 Filter budget reasons by regular expression',
    '  --out <file>                Output path for summary JSON',
    '  --csv <file>                Output path for export CSV',
    '  --fail-on-violation         Exit with non-zero status when budgets fail',
    '  --format json|text          Output format (json only)',
    '  --quiet                     Suppress diagnostics',
    '  --help                      Show this message'
  ];
  process.stdout.write(`${lines.join('\n')}\n`);
}

function compileGrep(pattern) {
  if (pattern === undefined) return undefined;
  try {
    return new RegExp(pattern, 'u');
  } catch (error) {
    const message = error instanceof Error ? error.message : String(error);
    logDiagnostic(`invalid --grep pattern: ${message}`, { force: true });
    printStatus({ ok: false, error: `invalid --grep pattern: ${message}` });
    process.exitCode = 1;
    return undefined;
  }
}

function formatNumber(value) {
  if (typeof value !== 'number') return '';
  if (Number.isInteger(value)) return value.toString();
  return value.toFixed(6).replace(/0+$/u, '').replace(/\.$/u, '');
}

function escapeCSV(value) {
  if (value === '') return '';
  if (/[",\n]/u.test(value)) {
    return `"${value.replace(/"/gu, '""')}"`;
  }
  return value;
}

function buildTraceCSV(records) {
  const header = ['ts', 'prim_id', 'effect', 'ms'];
  const rows = [header];
  for (const record of records) {
    rows.push([
      record.ts.toString(),
      record.prim_id,
      record.effect,
      record.ms === undefined ? '' : formatNumber(record.ms)
    ]);
  }
  const csv = rows.map((row) => row.map((value) => escapeCSV(value ?? '')).join(',')).join('\n');
  const csvWithNewline = `${csv}\n`;
  if (!csvWithNewline.startsWith(`${header.join(',')}`)) {
    throw new Error('CSV header missing');
  }
  if (!csvWithNewline.endsWith('\n')) {
    throw new Error('CSV must end with newline');
  }
  return { csv: csvWithNewline, dataRows: records.length, header: header.join(',') };
}

function buildSummaryCSV(summary) {
  const header = ['kind', 'name', 'count', 'ms'];
  const rows = [header];
  const totalCount = typeof summary.total === 'number' ? summary.total : 0;
  const totalMs = typeof summary.ms_total === 'number' ? summary.ms_total : 0;
  rows.push(['total', '', totalCount.toString(), formatNumber(totalMs)]);

  const byEffect = summary.by_effect && typeof summary.by_effect === 'object' ? summary.by_effect : {};
  const msByEffect = summary.ms_by_effect && typeof summary.ms_by_effect === 'object' ? summary.ms_by_effect : {};
  for (const key of Object.keys(byEffect).sort()) {
    const count = byEffect[key] ?? 0;
    const ms = msByEffect[key] ?? 0;
    rows.push(['effect', key, count.toString(), formatNumber(ms)]);
  }

  const byPrim = summary.by_prim && typeof summary.by_prim === 'object' ? summary.by_prim : {};
  for (const key of Object.keys(byPrim).sort()) {
    const count = byPrim[key] ?? 0;
    rows.push(['primitive', key, count.toString(), '']);
  }

  const csv = rows.map((row) => row.map((value) => escapeCSV(value ?? '')).join(',')).join('\n');
  const csvWithNewline = `${csv}\n`;
  if (!csvWithNewline.startsWith(`${header.join(',')}`)) {
    throw new Error('CSV header missing');
  }
  if (!csvWithNewline.endsWith('\n')) {
    throw new Error('CSV must end with newline');
  }
  return { csv: csvWithNewline, dataRows: rows.length - 1, header: header.join(',') };
}

async function ensureDirectory(target) {
  await mkdir(dirname(target), { recursive: true });
}

async function runValidate(args) {
  const input = getOption(args, '--in');
  if (!input) {
    logDiagnostic('missing --in', { force: true });
    printStatus({ ok: false, error: 'missing --in' });
    process.exitCode = 1;
    return;
  }

  const { records, errors } = await ingestTraceFile(input);
  const baseStatus = { count: records.length, errors_count: errors.length };

  if (errors.length > 0) {
    logDiagnostic(`validation failed for ${input}`, { force: true });
    printStatus({ ok: false, errors, ...baseStatus });
    process.exitCode = 1;
    return;
  }

  logDiagnostic(`validated ${records.length} record(s)`);
  printStatus({ ok: true, ...baseStatus });
}

async function runSummary(args) {
  const input = getOption(args, '--in');
  const output = getOption(args, '--out');
  if (!input || !output) {
    logDiagnostic('missing --in or --out', { force: true });
    printStatus({ ok: false, error: 'missing --in or --out' });
    process.exitCode = 1;
    return;
  }

  const { records, errors } = await ingestTraceFile(input);
  const baseStatus = { count: records.length, errors_count: errors.length };

  if (errors.length > 0) {
    logDiagnostic(`summary generation failed for ${input}`, { force: true });
    printStatus({ ok: false, errors, ...baseStatus });
    process.exitCode = 1;
    return;
  }

  const summary = summarizeTrace(records);
  const target = resolve(process.cwd(), output);
  await ensureDirectory(target);
  await writeFile(target, `${JSON.stringify(summary)}\n`, 'utf8');

  logDiagnostic(`wrote summary to ${output}`);
  const status = {
    ok: true,
    out: output,
    total: summary.total,
    ms_total: maybeRoundMs(summary.ms_total),
    ...baseStatus
  };
  printStatus(status);
}

async function loadSummaryFromFile(path) {
  let summaryRaw;
  try {
    summaryRaw = await readFile(path, 'utf8');
  } catch (error) {
    throw new Error(`cannot read summary: ${error instanceof Error ? error.message : String(error)}`);
  }

  try {
    return JSON.parse(summaryRaw);
  } catch (error) {
    throw new Error(`invalid summary JSON: ${error instanceof Error ? error.message : String(error)}`);
  }
}

function validateBudgetSpecShape(spec) {
  const errors = [];
  if (!spec || typeof spec !== 'object' || Array.isArray(spec)) {
    errors.push('spec must be an object');
    return errors;
  }

  const allowedTop = new Set(['total_ms_max', 'by_effect']);
  for (const key of Object.keys(spec)) {
    if (!allowedTop.has(key)) {
      errors.push(`unexpected top-level key: ${key}`);
    }
  }

  if (spec.by_effect !== undefined) {
    if (!spec.by_effect || typeof spec.by_effect !== 'object' || Array.isArray(spec.by_effect)) {
      errors.push('by_effect must be an object');
    } else {
      for (const [effect, rule] of Object.entries(spec.by_effect)) {
        if (!rule || typeof rule !== 'object' || Array.isArray(rule)) {
          errors.push(`by_effect.${effect} must be an object`);
          continue;
        }
        const allowedRuleKeys = new Set(['ms_max', 'count_max']);
        for (const key of Object.keys(rule)) {
          if (!allowedRuleKeys.has(key)) {
            errors.push(`unexpected key in by_effect.${effect}: ${key}`);
          }
        }
      }
    }
  }

  return errors;
}

async function runBudget(args) {
  const input = getOption(args, '--in');
  const summaryInput = getOption(args, '--summary-in');
  const specPath = getOption(args, '--spec') ?? getOption(args, '--budgets');

  if (!specPath) {
    logDiagnostic('missing --spec', { force: true });
    printStatus({ ok: false, error: 'missing --spec' });
    process.exitCode = 1;
    return;
  }

  if ((input && summaryInput) || (!input && !summaryInput)) {
    logDiagnostic('provide either --in or --summary-in', { force: true });
    printStatus({ ok: false, error: 'provide either --in or --summary-in' });
    process.exitCode = 1;
    return;
  }

  let summary;
  let baseStatus = { count: 0, errors_count: 0 };

  if (input) {
    const { records, errors } = await ingestTraceFile(input);
    baseStatus = { count: records.length, errors_count: errors.length };
    if (errors.length > 0) {
      logDiagnostic(`budget check failed during ingestion for ${input}`, { force: true });
      printStatus({ ok: false, errors, ...baseStatus });
      process.exitCode = 1;
      return;
    }
    summary = summarizeTrace(records);
  } else {
    try {
      summary = await loadSummaryFromFile(summaryInput);
    } catch (error) {
      const message = error instanceof Error ? error.message : String(error);
      logDiagnostic(message, { force: true });
      printStatus({ ok: false, error: message, ...baseStatus });
      process.exitCode = 1;
      return;
    }
    if (typeof summary?.total === 'number') {
      baseStatus = { count: summary.total, errors_count: 0 };
    }
  }

  let specRaw;
  try {
    specRaw = await readFile(specPath, 'utf8');
  } catch (error) {
    const message = `cannot read spec: ${error instanceof Error ? error.message : String(error)}`;
    logDiagnostic(message, { force: true });
    printStatus({ ok: false, error: message, ...baseStatus });
    process.exitCode = 1;
    return;
  }

  let spec;
  try {
    spec = JSON.parse(specRaw);
  } catch (error) {
    const message = `invalid spec JSON: ${error instanceof Error ? error.message : String(error)}`;
    logDiagnostic(message, { force: true });
    printStatus({ ok: false, error: message, ...baseStatus });
    process.exitCode = 1;
    return;
  }

  const specErrors = validateBudgetSpecShape(spec);
  if (specErrors.length > 0) {
    const message = `invalid budget spec: ${specErrors.join('; ')}`;
    logDiagnostic(message, { force: true });
    printStatus({ ok: false, error: message, ...baseStatus });
    process.exitCode = 2;
    return;
  }

  const result = evaluateBudget(summary, spec);
  const reasons = context.grepPattern ? result.reasons.filter((reason) => context.grepPattern.test(reason)) : result.reasons;
  const status = {
    ok: result.ok,
    reasons,
    total: summary.total,
    ms_total: maybeRoundMs(summary.ms_total),
    ...baseStatus,
    source: input ? 'trace' : 'summary'
  };

  if (!result.ok) {
    logDiagnostic('budget check failed', { force: true });
    printStatus(status);
    if (context.failOnViolation) {
      process.exitCode = 1;
    }
    return;
  }

  logDiagnostic('budget check passed');
  printStatus(status);
}

async function runExport(args) {
  const input = getOption(args, '--in');
  const summaryPath = getOption(args, '--summary');
  const csvPath = getOption(args, '--csv');

  if (!csvPath) {
    logDiagnostic('missing --csv', { force: true });
    printStatus({ ok: false, error: 'missing --csv' });
    process.exitCode = 1;
    return;
  }

  if ((input && summaryPath) || (!input && !summaryPath)) {
    logDiagnostic('provide either --in or --summary', { force: true });
    printStatus({ ok: false, error: 'provide either --in or --summary' });
    process.exitCode = 1;
    return;
  }

  const target = resolve(process.cwd(), csvPath);
  await ensureDirectory(target);

  if (input) {
    const { records, errors } = await ingestTraceFile(input);
    const baseStatus = { count: records.length, errors_count: errors.length };
    if (errors.length > 0) {
      logDiagnostic(`export failed during ingestion for ${input}`, { force: true });
      printStatus({ ok: false, errors, ...baseStatus });
      process.exitCode = 1;
      return;
    }

    const { csv, dataRows } = buildTraceCSV(records);
    await writeFile(target, csv, 'utf8');
    logDiagnostic(`wrote trace csv to ${csvPath}`);
    printStatus({ ok: true, csv: csvPath, out: csvPath, rows: dataRows, kind: 'trace', ...baseStatus });
    return;
  }

  let summary;
  try {
    summary = await loadSummaryFromFile(summaryPath);
  } catch (error) {
    const message = error instanceof Error ? error.message : String(error);
    logDiagnostic(message, { force: true });
    printStatus({ ok: false, error: message, count: 0, errors_count: 0 });
    process.exitCode = 1;
    return;
  }

  const { csv, dataRows } = buildSummaryCSV(summary);
  await writeFile(target, csv, 'utf8');
  logDiagnostic(`wrote summary csv to ${csvPath}`);
  printStatus({ ok: true, csv: csvPath, out: csvPath, rows: dataRows, kind: 'summary', count: summary.total ?? 0, errors_count: 0 });
}

async function main() {
  const argv = process.argv.slice(2);
  const { options, rest } = parseGlobalOptions(argv);
  context.quiet = options.quiet;
  context.failOnViolation = options.failOnViolation;
  context.outputFormat = options.format ?? 'json';

  if (options.help || rest.length === 0) {
    printHelp();
    return;
  }

  if (context.outputFormat !== 'json') {
    const message = `unsupported format: ${context.outputFormat}`;
    logDiagnostic(message, { force: true });
    printStatus({ ok: false, error: message });
    process.exitCode = 1;
    return;
  }

  const grepPattern = compileGrep(options.grep);
  if (options.grep !== undefined && grepPattern === undefined && process.exitCode) {
    return;
  }
  context.grepPattern = grepPattern;
  const command = rest[0];
  const commandArgs = rest.slice(1);

  switch (command) {
    case 'validate':
      await runValidate(commandArgs);
      break;
    case 'summary':
      await runSummary(commandArgs);
      break;
    case 'budget':
      await runBudget(commandArgs);
      break;
    case 'export':
      await runExport(commandArgs);
      break;
    default:
      logDiagnostic('unknown command', { force: true });
      printStatus({ ok: false, error: 'unknown command' });
      process.exitCode = 1;
  }
}

main().catch((error) => {
  const message = error instanceof Error ? error.message : String(error);
  logDiagnostic(message, { force: true });
  printStatus({ ok: false, error: message });
  process.exitCode = 1;
});
