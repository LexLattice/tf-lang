import { readFile } from 'node:fs/promises';

import { TraceRecord, ValidationIssue, validateTraceRecord } from './validate.js';

export interface TraceIngestError {
  line: number;
  message: string;
  issues?: ValidationIssue[];
  raw?: string;
}

export interface TraceIngestResult {
  records: TraceRecord[];
  errors: TraceIngestError[];
}

function parseLine(line: string, lineNumber: number): { ok: true; record: TraceRecord } | { ok: false; error: TraceIngestError } {
  let value: unknown;
  try {
    value = JSON.parse(line);
  } catch (error) {
    return {
      ok: false,
      error: {
        line: lineNumber,
        message: error instanceof Error ? error.message : 'invalid JSON',
        raw: line
      }
    };
  }

  const result = validateTraceRecord(value);
  if (!result.ok) {
    return {
      ok: false,
      error: {
        line: lineNumber,
        message: 'validation failed',
        issues: result.issues,
        raw: line
      }
    };
  }

  return { ok: true, record: result.record };
}

export async function ingestTraceFile(path: string): Promise<TraceIngestResult> {
  const content = await readFile(path, 'utf8');
  const lines = content.split(/\r?\n/);

  let lastDataIndex = -1;
  for (let i = lines.length - 1; i >= 0; i--) {
    if (lines[i].trim() !== '') {
      lastDataIndex = i;
      break;
    }
  }

  const strictEmpty = (() => {
    const value = process.env.TRACE_STRICT_EMPTY;
    if (!value) return false;
    if (value === '1') return true;
    return value.toLowerCase() === 'true';
  })();

  const records: TraceRecord[] = [];
  const errors: TraceIngestError[] = [];

  for (let i = 0; i < lines.length; i++) {
    const line = lines[i];
    if (line.trim() === '') {
      if (i <= lastDataIndex && strictEmpty) {
        errors.push({
          line: i + 1,
          message: 'Empty line',
          raw: line
        });
      }
      continue;
    }

    const outcome = parseLine(line, i + 1);
    if (outcome.ok) {
      records.push(outcome.record);
    } else {
      errors.push(outcome.error);
    }
  }

  return { records, errors };
}
