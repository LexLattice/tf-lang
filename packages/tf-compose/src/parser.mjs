// DSL parser (extended) supporting regions: authorize{ ... } and txn{ ... }
export function parseDSL(src) {
  const tokens = tokenize(src);
  const seq = parseSeq(tokens);
  expectEOF(tokens);
  return seq;
}

function tokenize(s) {
  const out = []; let i=0;
  while (i<s.length) {
    const c=s[i];
    if (/\s/.test(c)) { i++; continue; }
    if (s.startsWith('|>', i)) { out.push({t:'PIPE'}); i+=2; continue; }
    if (s.startsWith('par{', i)) { out.push({t:'PAR_OPEN'}); i+=4; continue; }
    if (s.startsWith('seq{', i)) { out.push({t:'SEQ_OPEN'}); i+=4; continue; }
    if (s.startsWith('authorize', i) && ['{','('].includes(s[i+9])) { out.push({t:'REGION_AUTH'}); i+=9; continue; }
    if (s.startsWith('txn', i) && ['{','('].includes(s[i+3])) { out.push({t:'REGION_TXN'}); i+=3; continue; }
    if (c==='{' ) { out.push({t:'LBRACE'}); i++; continue; }
    if (c==='}') { out.push({t:'RBRACE'}); i++; continue; }
    if (c==='(' ) { out.push({t:'LPAREN'}); i++; continue; }
    if (c===')' ) { out.push({t:'RPAREN'}); i++; continue; }
    if (c===';') { out.push({t:'SEMI'}); i++; continue; }
    if (c===',') { out.push({t:'COMMA'}); i++; continue; }
    if (c==='=') { out.push({t:'EQ'}); i++; continue; }
    if (c==='"' || c==="'" ) {
      const q=c; i++; let buf=''; while (i<s.length && s[i]!==q){ if(s[i]=='\\'){ buf+=s[i+1]; i+=2; } else { buf+=s[i++]; } }
      i++; out.push({t:'STRING', v:buf}); continue;
    }
    if (/[0-9]/.test(c)) { let j=i; while (j<s.length && /[0-9]/.test(s[j])) j++; out.push({t:'NUMBER', v:Number(s.slice(i,j))}); i=j; continue; }
    let j=i; while (j<s.length && /[A-Za-z0-9_\-\.]/.test(s[j])) j++;
    out.push({t:'IDENT', v:s.slice(i,j)}); i=j;
  }
  return {i:0, list:out};
}

function peek(t){ return t.list[t.i]||{t:'EOF'}; }
function take(t, kind){ const p=peek(t); if (p.t!==kind) throw new Error(`Expected ${kind}, got ${p.t}`); t.i++; return p; }
function maybe(t, kind){ const p=peek(t); if (p.t===kind){ t.i++; return true; } return false; }
function expectEOF(t){ if (peek(t).t!=='EOF') throw new Error('Trailing tokens'); }

function parseSeq(t){
  const parts=[parseStep(t)];
  while (maybe(t,'PIPE')) parts.push(parseStep(t));
  return parts.length===1 ? parts[0] : { node:'Seq', children: parts };
}

function parseBlock(t, node){
  const kids=[];
  while (true){
    kids.push(parseStep(t));
    if (maybe(t,'SEMI')) continue;
    take(t,'RBRACE'); break;
  }
  node.children = kids;
  return node;
}

function parseRegion(t, kind){
  // optional attrs: e.g., authorize(region="us", scope="kms.sign"){ ... }
  let attrs={};
  if (maybe(t,'LPAREN')) {
    if (!maybe(t,'RPAREN')) {
      while (true){
        const key = take(t,'IDENT').v;
        take(t,'EQ');
        const vTok=peek(t);
        let val;
        if (vTok.t==='STRING' || vTok.t==='NUMBER'){ take(t,vTok.t); val=vTok.v; }
        else if (vTok.t==='IDENT'){ take(t,'IDENT'); val=vTok.v; }
        else throw new Error('Bad region attr value');
        attrs[key]=val;
        if (maybe(t,'COMMA')) continue;
        take(t,'RPAREN'); break;
      }
    }
  }
  take(t,'LBRACE');
  return parseBlock(t, { node:'Region', kind, attrs, children: [] });
}

function parseStep(t){
  if (maybe(t,'PAR_OPEN')) return parseBlock(t, { node:'Par', children: [] });
  if (maybe(t,'SEQ_OPEN')) return parseBlock(t, { node:'Seq', children: [] });
  if (maybe(t,'REGION_AUTH')) return parseRegion(t, 'Authorize');
  if (maybe(t,'REGION_TXN')) return parseRegion(t, 'Transaction');
  const id = take(t,'IDENT').v;
  let args={};
  if (maybe(t,'LPAREN')) {
    if (!maybe(t,'RPAREN')) {
      while (true){
        const key = take(t,'IDENT').v;
        take(t,'EQ');
        const vTok=peek(t);
        let val;
        if (vTok.t==='STRING' || vTok.t==='NUMBER'){ take(t,vTok.t); val=vTok.v; }
        else if (vTok.t==='IDENT'){ take(t,'IDENT'); val=vTok.v; }
        else throw new Error('Bad arg value');
        args[key]=val;
        if (maybe(t,'COMMA')) continue;
        take(t,'RPAREN'); break;
      }
    }
  }
  return { node:'Prim', prim: id.toLowerCase(), args };
}
