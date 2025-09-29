export interface TraceRecord {
  ts: number;
  prim_id: string;
  effect: string;
  ms?: number;
}

export interface ValidationIssue {
  path: string;
  message: string;
}

export type ValidationResult =
  | { ok: true; record: TraceRecord }
  | { ok: false; issues: ValidationIssue[] };

function isNumber(value: unknown): value is number {
  return typeof value === 'number' && Number.isFinite(value);
}

function isString(value: unknown): value is string {
  return typeof value === 'string';
}

export function validateTraceRecord(value: unknown): ValidationResult {
  const issues: ValidationIssue[] = [];

  if (value === null || typeof value !== 'object' || Array.isArray(value)) {
    return {
      ok: false,
      issues: [
        {
          path: '',
          message: 'record must be an object'
        }
      ]
    };
  }

  const record = value as Record<string, unknown>;

  if (!('ts' in record)) {
    issues.push({ path: '.ts', message: 'ts is required' });
  } else if (!isNumber(record.ts)) {
    issues.push({ path: '.ts', message: 'ts must be a finite number' });
  }

  if (!('prim_id' in record)) {
    issues.push({ path: '.prim_id', message: 'prim_id is required' });
  } else if (!isString(record.prim_id) || record.prim_id.length === 0) {
    issues.push({ path: '.prim_id', message: 'prim_id must be a non-empty string' });
  }

  if (!('effect' in record)) {
    issues.push({ path: '.effect', message: 'effect is required' });
  } else if (!isString(record.effect) || record.effect.length === 0) {
    issues.push({ path: '.effect', message: 'effect must be a non-empty string' });
  }

  if ('ms' in record) {
    const valueMs = record.ms;
    if (valueMs === null || valueMs === undefined) {
      issues.push({ path: '.ms', message: 'ms must be a number when provided' });
    } else if (!isNumber(valueMs)) {
      issues.push({ path: '.ms', message: 'ms must be a finite number' });
    } else if (valueMs < 0) {
      issues.push({ path: '.ms', message: 'ms must be greater than or equal to 0' });
    }
  }

  const allowedKeys = new Set(['ts', 'prim_id', 'effect', 'ms']);
  for (const key of Object.keys(record)) {
    if (!allowedKeys.has(key)) {
      issues.push({ path: `.${key}`, message: 'unexpected property' });
    }
  }

  if (issues.length > 0) {
    return { ok: false, issues };
  }

  const normalized: TraceRecord = {
    ts: record.ts as number,
    prim_id: record.prim_id as string,
    effect: record.effect as string
  };

  if ('ms' in record) {
    normalized.ms = record.ms as number;
  }

  return { ok: true, record: normalized };
}
