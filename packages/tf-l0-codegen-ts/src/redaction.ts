export type RedactionPolicy = { hashFields?: string[]; maskFields?: string[]; mask?: string; };
function sha256(s: string): string { return 'sha256:' + require('node:crypto').createHash('sha256').update(s).digest('hex'); }
function envList(name: string): string[] { const v=process.env[name]; return v? v.split(',').map(s=>s.trim()).filter(Boolean):[]; }
export function applyRedaction(evt: any, policy?: RedactionPolicy): any {
  const clone = JSON.parse(JSON.stringify(evt));
  const hashFields = new Set([...(policy?.hashFields||[]), ...envList('TF_TRACE_HASH_FIELDS')]);
  const maskFields = new Set([...(policy?.maskFields||[]), ...envList('TF_TRACE_MASK_FIELDS')]);
  const mask = policy?.mask ?? '***';
  if (process.env.TF_TRACE_REDACT==='1') ['idempotency_key','resource_uri','etag'].forEach(k=>hashFields.add(k));
  for (const k of hashFields) if (clone[k]!=null) clone[k]=sha256(String(clone[k]));
  for (const k of maskFields) if (clone[k]!=null) clone[k]=mask;
  return clone;
}
