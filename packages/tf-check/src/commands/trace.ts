import { spawn } from 'node:child_process';
import path from 'node:path';
import * as readline from 'node:readline';

import { openSink } from '../sink/jsonl.js';
import { parseFilters, compilePredicate, type Event } from '../filters.js';

export type TraceArgs = {
  runtime: 'ts' | 'rust';
  out: string;
  filter: string[];
  limit: number;
  follow: boolean;
  pred?: string;
  cwd: string;
  cmd?: string;
};

function defaultCommand(runtime: 'ts' | 'rust'): string {
  if (runtime === 'ts') {
    return 'node packages/tf-lang-l0-ts/dist/smoke-trace.js';
  }
  return 'cargo run -q --example trace-smoke --features dev_proofs';
}

function toCommandAndArgs(s: string): [string, string[]] {
  const parts = s.split(/\s+/);
  return [parts[0], parts.slice(1)];
}

export async function runTrace(args: TraceArgs): Promise<number> {
  const filters = parseFilters(args.filter ?? []);
  const predicate = compilePredicate(args.pred);
  const target = args.cmd ?? defaultCommand(args.runtime);

  // Minimal guard if you keep supporting --cmd
  if(/[\|\&;\$\(\)\{\}><`]/.test(target)){
    throw new Error('Illegal characters in --cmd');
  }

  const [cmd, cmdArgs] = toCommandAndArgs(target);
  const child = spawn(cmd, cmdArgs, {
    cwd: args.cwd,
    shell: false,
    env: { ...process.env, DEV_PROOFS: '1', TF_TRACE_STDOUT: '1' },
    stdio: ['ignore', 'pipe', 'inherit'],
  });

  const outPath = args.out === '-' ? '-' : path.resolve(args.cwd, args.out);
  const sink = await openSink(outPath);
  const rl = readline.createInterface({ input: child.stdout });

  let seen = 0;
  try {
    for await (const line of rl) {
      if (!line) continue;
      let event: Event;
      try {
        event = JSON.parse(line);
      } catch {
        continue;
      }
      if (filters(event) && predicate(event)) {
        await sink.write(event);
        seen += 1;
        if (args.limit > 0 && seen >= args.limit) {
          child.kill('SIGINT');
          break;
        }
      }
    }
  } finally {
    rl.close();
  }

  let code: number | null = null;
  let signal: NodeJS.Signals | null = null;
  try {
    const result = await new Promise<{ code: number | null; signal: NodeJS.Signals | null }>((resolve, reject) => {
      child.once('error', reject);
      child.once('close', (c, s) => resolve({ code: c, signal: s }));
    });
    code = result.code;
    signal = result.signal;
  } finally {
    await sink.close();
  }

  if (signal) {
    return 0;
  }
  return code ?? 0;
}
