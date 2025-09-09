
export interface Program {
  version: string;
  regs: number;
  instrs: Instr[];
}

export type Instr =
  | { op: 'HALT' }
  | { op: 'CONST', dst: number, value: unknown }
  | { op: 'PACK', dst: number, tag: string, regs: number[] }
  | { op: 'UNPACK', dsts: number[], tag: string, src: number }
  | { op: 'ID_HASH', dst: number, src: number }
  | { op: 'SNAP_MAKE', dst: number, state: number }
  | { op: 'SNAP_ID', dst: number, snapshot: number }
  | { op: 'LENS_PROJ', dst: number, state: number, region: string }
  | { op: 'LENS_MERGE', dst: number, state: number, region: string, sub: number }
  | { op: 'PLAN_SIM', dst_delta: number, dst_world: number, world: number, plan: number }
  | { op: 'DIFF_APPLY', dst: number, state: number, delta: number }
  | { op: 'DIFF_INVERT', dst: number, delta: number }
  | { op: 'JOURNAL_REC', dst: number, plan: number, delta: number, snap0: number, snap1: number, meta: number }
  | { op: 'JOURNAL_REW', dst: number, world: number, entry: number }
  | { op: 'CALL', dst: number, tf_id: string, args: number[] }
  | { op: 'ASSERT', pred: number, msg: string };
