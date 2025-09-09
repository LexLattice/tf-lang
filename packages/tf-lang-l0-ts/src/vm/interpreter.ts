
import type { Program, Instr } from '../model/bytecode.js';
import type { Host } from './opcode.js';
import type { Value, World, JournalEntry } from '../model/types.js';
import { canonicalJson, contentHash } from '../hash.js';

export class VM {
  constructor(public host: Host) {}

  private get(regs: Value[], idx: number): Value {
    if (idx < 0 || idx >= regs.length) throw new Error(`register out of bounds: r${idx}`);
    return regs[idx];
  }

  async run(prog: Program): Promise<Value> {
    const regs: Value[] = Array.from({ length: prog.regs }, () => null);

    for (const ins of prog.instrs) {
      switch (ins.op) {
        case 'HALT': break;
        case 'CONST': regs[ins.dst] = structuredClone(ins.value); break;
        case 'PACK': {
          const arr = ins.regs.map(r => structuredClone(this.get(regs, r)));
          regs[ins.dst] = { tag: ins.tag, values: arr };
          break;
        }
        case 'UNPACK': {
          const v = this.get(regs, ins.src);
          if (!v || typeof v !== 'object' || v.tag !== ins.tag || !Array.isArray(v.values)) {
            throw new Error('UNPACK expects {tag,values[]} with matching tag');
          }
          if (v.values.length !== ins.dsts.length) throw new Error('UNPACK arity mismatch');
          v.values.forEach((vv: any, i: number) => { regs[ins.dsts[i]] = structuredClone(vv); });
          break;
        }
        case 'ID_HASH': {
          const json = canonicalJson(this.get(regs, ins.src));
          regs[ins.dst] = contentHash(json);
          break;
        }
        case 'SNAP_MAKE': regs[ins.dst] = await this.host.snapshot_make(this.get(regs, ins.state)); break;
        case 'SNAP_ID': regs[ins.dst] = await this.host.snapshot_id(this.get(regs, ins.snapshot)); break;
        case 'LENS_PROJ': regs[ins.dst] = await this.host.lens_project(this.get(regs, ins.state), ins.region); break;
        case 'LENS_MERGE': regs[ins.dst] = await this.host.lens_merge(this.get(regs, ins.state), ins.region, this.get(regs, ins.sub)); break;
        case 'PLAN_SIM': {
          const res: any = await this.host.call_tf("tf://plan/simulate@0.1", [this.get(regs, ins.world), this.get(regs, ins.plan)]);
          regs[ins.dst_delta] = res?.delta ?? null;
          regs[ins.dst_world] = res?.world ?? null;
          break;
        }
        case 'DIFF_APPLY': regs[ins.dst] = await this.host.diff_apply(this.get(regs, ins.state), this.get(regs, ins.delta)); break;
        case 'DIFF_INVERT': regs[ins.dst] = await this.host.diff_invert(this.get(regs, ins.delta)); break;
        case 'JOURNAL_REC': {
          const s0 = this.get(regs, ins.snap0); if (typeof s0 !== 'string') throw new Error('snap0 not string');
          const s1 = this.get(regs, ins.snap1); if (typeof s1 !== 'string') throw new Error('snap1 not string');
          const je = await this.host.journal_record(this.get(regs, ins.plan), this.get(regs, ins.delta), s0, s1, this.get(regs, ins.meta));
          regs[ins.dst] = je.value;
          break;
        }
        case 'JOURNAL_REW': {
          const w: World = { value: this.get(regs, ins.world) };
          const j: JournalEntry = { value: this.get(regs, ins.entry) };
          const prev = await this.host.journal_rewind(w, j);
          regs[ins.dst] = prev.value;
          break;
        }
        case 'CALL': {
          const args = ins.args.map(a => this.get(regs, a));
          regs[ins.dst] = await this.host.call_tf(ins.tf_id, args);
          break;
        }
        case 'ASSERT': {
          const v = this.get(regs, ins.pred);
          if (v !== true) throw new Error(`ASSERT failed: ${ins.msg}`);
          break;
        }
        default: {
          const _: never = ins;
          throw new Error('unknown opcode');
        }
      }
    }

    return regs[0] ?? null;
  }
}
