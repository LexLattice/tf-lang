export const Effects = ["Pure","Time.Read","Time.Wait","Randomness.Read","Network.In","Network.Out","Storage.Read","Storage.Write","Crypto","Policy","Observability"];
export function unionEffects(a=[], b=[]) { return Array.from(new Set([...(a||[]), ...(b||[])])); }
