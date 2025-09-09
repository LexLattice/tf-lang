
export type SnapshotId = string;
export type Region = string;
export type Capability = string;

export class Effects {
  reads: Set<Region> = new Set();
  writes: Set<Region> = new Set();
  addRead(r: Region) { this.reads.add(r); return this; }
  addWrite(r: Region) { this.writes.add(r); return this; }
  isSubsetOf(other: Effects): boolean {
    return [...this.reads].every(r => other.reads.has(r)) &&
           [...this.writes].every(r => other.writes.has(r));
  }
  static from(reads: Region[] = [], writes: Region[] = []) {
    const e = new Effects();
    reads.forEach(r => e.addRead(r)); writes.forEach(w => e.addWrite(w));
    return e;
  }
}

export interface Manifest {
  tf_id: string;
  inputs: string[];
  output: string;
  declared_effects: { reads: string[], writes: string[] };
  bytecode_hash: string;
  sig_hash: string;
}

export type Value = any;
export interface World { value: Value }
export interface JournalEntry { value: Value }

export class TfRegistry {
  private funcs = new Map<string, (args: Value[]) => Value | Promise<Value>>();
  register(id: string, f: (args: Value[]) => Value | Promise<Value>) {
    this.funcs.set(id, f); return this;
  }
  async call(id: string, args: Value[]): Promise<Value> {
    const f = this.funcs.get(id);
    if (!f) throw new Error(`unknown tf: ${id}`);
    return await f(args);
  }
}
