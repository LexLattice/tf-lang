
import type { Value, World, JournalEntry } from '../model/types.js';

export interface Host {
  lens_project(state: Value, region: string): Value | Promise<Value>;
  lens_merge(state: Value, region: string, substate: Value): Value | Promise<Value>;

  snapshot_make(state: Value): Value | Promise<Value>;
  snapshot_id(snapshot: Value): string | Promise<string>;

  diff_apply(state: Value, delta: Value): Value | Promise<Value>;
  diff_invert(delta: Value): Value | Promise<Value>;

  journal_record(plan: Value, delta: Value, s0: string, s1: string, meta: Value): JournalEntry | Promise<JournalEntry>;
  journal_rewind(world: World, entry: JournalEntry): World | Promise<World>;

  call_tf(tf_id: string, args: Value[]): Value | Promise<Value>;
}
