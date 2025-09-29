function formatNumber(value) {
    return Number.isInteger(value) ? value.toString() : value.toFixed(3).replace(/0+$/u, '').replace(/\.$/u, '');
}
export function evaluateBudget(summary, spec) {
    const reasonsCollected = [];
    if (typeof spec.total_ms_max === 'number') {
        if (summary.ms_total > spec.total_ms_max) {
            reasonsCollected.push({
                effect: '',
                metric: 'total_ms',
                message: `total ms ${formatNumber(summary.ms_total)} exceeds limit ${formatNumber(spec.total_ms_max)}`
            });
        }
    }
    if (spec.by_effect && typeof spec.by_effect === 'object') {
        const effectKeys = Object.keys(spec.by_effect).sort();
        for (const key of effectKeys) {
            const rule = spec.by_effect[key];
            if (!rule || typeof rule !== 'object')
                continue;
            if (typeof rule.count_max === 'number') {
                const count = summary.by_effect[key] ?? 0;
                if (count > rule.count_max) {
                    reasonsCollected.push({
                        effect: key,
                        metric: 'count',
                        message: `effect ${key} count ${count} exceeds limit ${rule.count_max}`
                    });
                }
            }
            if (typeof rule.ms_max === 'number') {
                const ms = summary.ms_by_effect[key] ?? 0;
                if (ms > rule.ms_max) {
                    reasonsCollected.push({
                        effect: key,
                        metric: 'ms',
                        message: `effect ${key} ms ${formatNumber(ms)} exceeds limit ${formatNumber(rule.ms_max)}`
                    });
                }
            }
        }
    }
    reasonsCollected.sort((a, b) => {
        if (a.effect === b.effect) {
            return a.metric.localeCompare(b.metric);
        }
        return a.effect.localeCompare(b.effect);
    });
    const reasons = reasonsCollected.map((entry) => entry.message);
    return { ok: reasons.length === 0, reasons };
}
