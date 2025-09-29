function toSortedObject(map) {
    const entries = Array.from(map.entries()).sort(([a], [b]) => (a < b ? -1 : a > b ? 1 : 0));
    const output = {};
    for (const [key, value] of entries) {
        output[key] = value;
    }
    return output;
}
export function summarizeTrace(records) {
    const byEffect = new Map();
    const byPrim = new Map();
    const msByEffect = new Map();
    let msTotal = 0;
    for (const record of records) {
        byEffect.set(record.effect, (byEffect.get(record.effect) ?? 0) + 1);
        byPrim.set(record.prim_id, (byPrim.get(record.prim_id) ?? 0) + 1);
        if (typeof record.ms === 'number') {
            msTotal += record.ms;
            msByEffect.set(record.effect, (msByEffect.get(record.effect) ?? 0) + record.ms);
        }
    }
    return {
        total: records.length,
        by_effect: toSortedObject(byEffect),
        by_prim: toSortedObject(byPrim),
        ms_total: msTotal,
        ms_by_effect: toSortedObject(msByEffect)
    };
}
