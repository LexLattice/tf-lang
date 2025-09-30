export function summarizeEffects(doc = {}) {
  const effects = doc?.effects;
  if (typeof effects === "string") {
    if (effects.trim().length > 0) {
      return effects;
    }
  }
  if (Array.isArray(effects)) {
    if (effects.length > 0) {
      return effects.join("+");
    }
  }
  if (effects && typeof effects === "object") {
    const keys = Object.keys(effects);
    if (keys.length > 0) {
      return keys.join("+");
    }
  }
  const nodes = Array.isArray(doc?.nodes) ? doc.nodes : [];
  const kindToEffect = new Map([
    ["Publish", "Outbound"],
    ["Subscribe", "Inbound"],
    ["Keypair", "Entropy"],
    ["Transform", "Pure"],
  ]);
  const preferredOrder = ["Outbound", "Inbound", "Entropy", "Pure"];
  const seen = new Set();
  for (const node of nodes) {
    const effect = kindToEffect.get(node?.kind);
    if (effect) {
      seen.add(effect);
    }
  }
  const inferred = preferredOrder.filter((effect) => seen.has(effect));
  if (inferred.length > 0) {
    return inferred.join("+");
  }
  return "";
}
