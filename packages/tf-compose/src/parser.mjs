// Tiny DSL parser: supports pipes `|>` and simple par blocks: par{ a(); b(args=1) }
export function parseDSL(src) {
  const tokens = tokenize(src);
  const seq = parseSeq(tokens);
  expectEOF(tokens);
  return seq;
}

function tokenize(s) {
  // Very small tokenizer suitable for samples.
  const out = [];
  let i=0;
  while (i < s.length) {
    const c = s[i];
    if (/\s/.test(c)) { i++; continue; }
    if (s.startsWith('|>', i)) { out.push({t:'PIPE'}); i+=2; continue; }
    if (s.startsWith('par{', i)) { out.push({t:'PAR_OPEN'}); i+=4; continue; }
    if (c === '{') { out.push({t:'LBRACE'}); i++; continue; }
    if (c === '}') { out.push({t:'RBRACE'}); i++; continue; }
    if (c === '(') { out.push({t:'LPAREN'}); i++; continue; }
    if (c === ')') { out.push({t:'RPAREN'}); i++; continue; }
    if (c === ';') { out.push({t:'SEMI'}); i++; continue; }
    if (c === ',') { out.push({t:'COMMA'}); i++; continue; }
    if (c === '=') { out.push({t:'EQ'}); i++; continue; }
    if (c === '"' || c === "'") {
      const q=c; i++; let buf=''; while (i<s.length && s[i]!==q){ if(s[i]=='\\'){ buf+=s[i+1]; i+=2;} else {buf+=s[i++];} }
      i++; out.push({t:'STRING', v:buf}); continue;
    }
    if (/[0-9]/.test(c)) {
      let j=i; while (j<s.length && /[0-9]/.test(s[j])) j++;
      out.push({t:'NUMBER', v:Number(s.slice(i,j))}); i=j; continue;
    }
    // ident
    let j=i; while (j<s.length && /[A-Za-z0-9_\-\.]/.test(s[j])) j++;
    out.push({t:'IDENT', v:s.slice(i,j)}); i=j;
  }
  return { i:0, list: out };
}

function peek(t){ return t.list[t.i]||{t:'EOF'}; }
function take(t, kind){ const p=peek(t); if (p.t!==kind) throw new Error(`Expected ${kind}, got ${p.t}`); t.i++; return p; }
function maybe(t, kind){ const p=peek(t); if (p.t===kind){ t.i++; return true;} return false; }
function expectEOF(t){ if (peek(t).t!=='EOF') throw new Error('Trailing tokens'); }

function parseSeq(t){
  const parts=[parseStep(t)];
  while (maybe(t,'PIPE')) parts.push(parseStep(t));
  if (parts.length===1) return parts[0];
  return { node:'Seq', children: parts };
}

function parseStep(t){
  if (maybe(t,'PAR_OPEN')) {
    const kids=[];
    while (true){
      kids.push(parseStep(t));
      if (maybe(t,'SEMI')) continue;
      const r=take(t,'RBRACE'); break;
    }
    return { node:'Par', children: kids };
  }
  // Prim(args?)
  const id = take(t,'IDENT').v;
  let args={};
  if (maybe(t,'LPAREN')) {
    if (!maybe(t,'RPAREN')) {
      while (true){
        const key = take(t,'IDENT').v;
        take(t,'EQ');
        const valTok = peek(t);
        let val;
        if (valTok.t==='STRING' || valTok.t==='NUMBER') { take(t,valTok.t); val = valTok.v; }
        else if (valTok.t==='IDENT') { take(t,'IDENT'); val = valTok.v; }
        else throw new Error('Bad arg value');
        args[key]=val;
        if (maybe(t,'COMMA')) continue;
        take(t,'RPAREN'); break;
      }
    }
  }
  return { node:'Prim', prim: id.toLowerCase(), args };
}
