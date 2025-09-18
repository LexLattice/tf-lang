export function ok(value, warnings) {
    return {
        ok: true,
        value,
        ...(warnings ? { warnings: normalizeWarnings(warnings) } : {}),
    };
}
export function err(code, explain, details) {
    return {
        ok: false,
        error: {
            code: normalizeCode(code),
            explain: explain.trim(),
            ...(details === undefined ? {} : { details }),
        },
    };
}
export function withTrace(base, trace) {
    const existing = base.trace ?? [];
    const merged = normalizeWarnings([...existing, ...trace]);
    if (merged.length === 0) {
        return { ...base, trace: undefined };
    }
    return {
        ...base,
        trace: merged,
    };
}
function normalizeWarnings(source) {
    const set = new Set();
    for (const entry of source) {
        const normalized = entry.trim();
        if (normalized.length > 0) {
            set.add(normalized);
        }
    }
    return Array.from(set.values()).sort((a, b) => {
        if (a < b) {
            return -1;
        }
        if (a > b) {
            return 1;
        }
        return 0;
    });
}
function normalizeCode(code) {
    const normalized = code.trim();
    if (!normalized) {
        return "E_UNKNOWN";
    }
    return normalized.toUpperCase();
}
