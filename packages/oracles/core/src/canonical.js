export const defaultCanonicalize = (value) => {
    return canonicalizeValue(value);
};
export function canonicalStringify(value) {
    return JSON.stringify(canonicalizeValue(value));
}
function canonicalizeValue(value) {
    if (value === null) {
        return null;
    }
    const valueType = typeof value;
    if (valueType === "number") {
        return canonicalizeNumber(value);
    }
    if (valueType === "string" || valueType === "boolean") {
        return value;
    }
    if (valueType === "bigint") {
        return value.toString(10);
    }
    if (valueType === "symbol") {
        return String(value);
    }
    if (valueType === "function") {
        return `[fn ${String(value.name || "anonymous")}]`;
    }
    if (Array.isArray(value)) {
        return value.map((entry) => canonicalizeValue(entry ?? null));
    }
    if (value instanceof Set) {
        const canonicalItems = Array.from(value).map((entry) => canonicalizeValue(entry ?? null));
        canonicalItems.sort((left, right) => {
            const a = JSON.stringify(left);
            const b = JSON.stringify(right);
            if (a < b) {
                return -1;
            }
            if (a > b) {
                return 1;
            }
            return 0;
        });
        return canonicalItems;
    }
    if (value instanceof Date) {
        return value.toISOString();
    }
    if (value && typeof value.toJSON === "function") {
        return canonicalizeValue(value.toJSON());
    }
    if (value && valueType === "object") {
        const input = value;
        const entries = Object.entries(input)
            .filter(([, entryValue]) => entryValue !== undefined)
            .map(([key, entryValue]) => [key, canonicalizeValue(entryValue)])
            .sort(([a], [b]) => (a < b ? -1 : a > b ? 1 : 0));
        const result = {};
        for (const [key, entryValue] of entries) {
            result[key] = entryValue;
        }
        return result;
    }
    return value;
}
function canonicalizeNumber(value) {
    if (!Number.isFinite(value)) {
        return value.toString();
    }
    const formatted = value.toFixed(12);
    const numeric = Number.parseFloat(formatted);
    return Object.is(numeric, -0) ? 0 : numeric;
}
