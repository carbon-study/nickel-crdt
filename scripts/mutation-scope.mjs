// Fail-closed mutation scoping for the Rust source under proof.
//
// A mutation names an item header (for example `fn plan(`) and an exact anchor
// string. Preparation refuses unless the header occurs exactly once in code and
// the anchor occurs exactly once inside that item's brace-matched body, entirely
// in code. "Code" is decided by a small lexer that blanks comments and string,
// char, byte, C-string and raw-string literals, so neither headers, anchors nor
// braces inside them count. Source the lexer cannot classify (unknown literal
// prefixes, unclassifiable quotes, unterminated literals or comments) is
// refused rather than guessed. The guarantee is narrow: exactly one edit inside
// the intended item. Whether that edit is still the named semantic fault is a
// review obligation.
import assert from 'node:assert/strict';

const identStart = c => c !== undefined && /[A-Za-z_]/.test(c);
const ident = c => c !== undefined && /[A-Za-z0-9_]/.test(c);
const CHAR = /^'(?:[^'\\\n]|\\(?:[nrt\\0'"]|x[0-9a-fA-F]{2}|u\{[0-9a-fA-F]{1,6}\}))'/;
const LIFETIME = /^'[A-Za-z_][A-Za-z0-9_]*/;
// Literal prefixes Rust accepts before a quote; any other identifier directly
// before `"`, `'` or `#"` is a reserved prefix and is refused.
const STRING_PREFIXES = new Set(['b', 'c', 'r', 'br', 'cr']);

// The source with every comment and literal replaced by spaces (newlines kept),
// so offsets line up with the original.
export function codeMask(source, where = 'source') {
  const out = source.split('');
  const blank = (from, to) => { for (let k = from; k < to; k++) if (out[k] !== '\n') out[k] = ' '; };
  const quoted = (open) => { // ordinary (escaped) string starting at the quote
    for (let j = open + 1; j < source.length; j++) {
      if (source[j] === '\\') j++;
      else if (source[j] === '"') return j + 1;
    }
    throw new Error(`${where}: unterminated string literal`);
  };
  const raw = (at) => { // at points at the first `#` or `"` after the r
    const m = /^(#*)"/.exec(source.slice(at, at + 258));
    if (!m) throw new Error(`${where}: malformed raw string at offset ${at}`);
    const close = '"' + m[1], end = source.indexOf(close, at + m[0].length);
    if (end < 0) throw new Error(`${where}: unterminated raw string`);
    return end + close.length;
  };
  const char = (at) => {
    const m = CHAR.exec(source.slice(at, at + 12));
    if (!m) throw new Error(`${where}: unsupported quote at offset ${at}`);
    return at + m[0].length;
  };
  let i = 0;
  while (i < source.length) {
    const c = source[i];
    if (source.startsWith('//', i)) { const nl = source.indexOf('\n', i); const end = nl < 0 ? source.length : nl; blank(i, end); i = end; continue; }
    if (source.startsWith('/*', i)) {
      let depth = 0, j = i;
      for (;;) {
        if (j >= source.length) throw new Error(`${where}: unterminated block comment`);
        if (source.startsWith('/*', j)) { depth++; j += 2; }
        else if (source.startsWith('*/', j)) { depth--; j += 2; if (depth === 0) break; }
        else j++;
      }
      blank(i, j); i = j; continue;
    }
    if (identStart(c) && !ident(source[i - 1])) {
      let j = i; while (ident(source[j])) j++;
      const word = source.slice(i, j), next = source[j];
      const rawNext = next === '#' && /^#+"/.test(source.slice(j, j + 258));
      if (next === '"' || rawNext) {
        if (!STRING_PREFIXES.has(word)) throw new Error(`${where}: unsupported literal prefix ${word} at offset ${i}`);
        const end = word.includes('r') ? raw(j) : (rawNext ? (() => { throw new Error(`${where}: malformed literal ${word}# at offset ${i}`); })() : quoted(j));
        blank(i, end); i = end; continue;
      }
      if (next === "'") {
        if (word !== 'b') throw new Error(`${where}: unsupported literal prefix ${word} at offset ${i}`);
        const end = char(j); blank(i, end); i = end; continue;
      }
      i = j; continue; // ordinary identifier, keyword or raw identifier r#name
    }
    if (/[0-9]/.test(c) && !ident(source[i - 1])) { let j = i; while (ident(source[j])) j++; i = j; continue; }
    if (c === '"') { const end = quoted(i); blank(i, end); i = end; continue; }
    if (c === "'") {
      const tail = source.slice(i, i + 12);
      if (CHAR.test(tail)) { const end = char(i); blank(i, end); i = end; continue; }
      const life = LIFETIME.exec(tail);
      if (life && source[i + life[0].length] !== "'") { i += life[0].length; continue; }
      throw new Error(`${where}: unsupported quote at offset ${i}`);
    }
    i++;
  }
  return out.join('');
}

// [start, end) of the item whose header occurs exactly once in code, on token
// boundaries.
export function itemSpan(source, header, where = header) {
  const code = codeMask(source, where), hits = [];
  for (let at = code.indexOf(header); at >= 0; at = code.indexOf(header, at + 1)) {
    const before = ident(header[0]) && ident(code[at - 1]);
    const after = ident(header.at(-1)) && ident(code[at + header.length]);
    if (!before && !after) hits.push(at);
  }
  assert(hits.length > 0, `${where}: mutation scope not found: ${header}`);
  assert.equal(hits.length, 1, `${where}: ambiguous mutation scope: ${header}`);
  // The header's own body must open before the declaration can end: reaching a
  // `;` (outside parentheses/brackets, e.g. not `[u8; 4]`) or a `}` first means a
  // bodyless declaration, and a `{` nested in the signature is an unsupported
  // shape. Both refuse instead of borrowing a later item's body.
  let open = -1, nest = (header.match(/[([]/g) ?? []).length - (header.match(/[)\]]/g) ?? []).length;
  for (let i = hits[0] + header.length; i < code.length && open < 0; i++) {
    const c = code[i];
    if (c === '(' || c === '[') nest++;
    else if (c === ')' || c === ']') nest--;
    else if (c === '{') { assert.equal(nest, 0, `${where}: unsupported brace in item signature: ${header}`); open = i; }
    else if (c === ';' && nest <= 0) throw new Error(`${where}: item declaration ends before its body: ${header}`);
    else if (c === '}') throw new Error(`${where}: item declaration ends before its body: ${header}`);
  }
  assert(open >= 0, `${where}: mutation scope has no complete body: ${header}`);
  let depth = 0;
  for (let i = open; i < code.length; i++) {
    if (code[i] === '{') depth++;
    else if (code[i] === '}') { depth--; assert(depth >= 0, `${where}: unbalanced braces in scope`); if (depth === 0) return [hits[0], i + 1, code]; }
  }
  throw new Error(`${where}: mutation scope has no complete body: ${header}`);
}

// Offset of the single anchor occurrence inside the named item, entirely in code.
export function scopedAnchor(source, header, needle, where) {
  const [start, end, code] = itemSpan(source, header, where);
  const body = source.slice(start, end), at = body.indexOf(needle);
  assert(at >= 0, `${where}: mutation anchor not found in its scope`);
  assert.equal(body.indexOf(needle, at + 1), -1, `${where}: mutation anchor is ambiguous in its scope`);
  assert.equal(code.slice(start + at, start + at + needle.length), needle, `${where}: mutation anchor is not code`);
  return start + at;
}

// Controls through the caller's actual preparation path. `prepare(mode, source)`
// must return the mutated source or throw. They build variants of the real file.
export function checkMutationScopeControls(prepare, source, mode, header, needle, later) {
  const [start, end] = itemSpan(source, header, 'control');
  const body = source.slice(start, end), name = /fn (\w+)\(/.exec(header)[1];
  assert.equal(body.split(needle).length, 2, 'control precondition: one anchor in the control scope');
  assert(source.slice(end).includes(needle), 'control precondition: the anchor text also occurs after its scope');
  const [laterStart, laterEnd] = itemSpan(source, later, 'control');
  assert(laterStart > end && source.slice(laterStart, laterEnd).includes(needle), 'control precondition: a later item contains the anchor');
  const variant = replacement => source.slice(0, start) + replacement + source.slice(end);
  const spelled = needle.replace('(', '::<(), Error>(');
  const refuses = (text, pattern, label) =>
    assert.throws(() => prepare(mode, text), pattern, `control ${label}: preparation must refuse`);
  // The anchor leaves its function but survives elsewhere: must not silently move.
  refuses(variant(body.replace(needle, spelled)), /anchor not found in its scope/, 'moved anchor');
  // A second copy inside the function, or the only copy inside a comment.
  refuses(variant(body.replace('{', '{\n    ' + needle + ';')), /anchor is ambiguous/, 'duplicate anchor');
  refuses(variant(body.replace(needle, spelled + ' /* ' + needle + ' */')), /anchor is not code/, 'anchor only in a comment');
  // The function is renamed away (with its calls), even when its old header
  // survives in a comment or string; or the header appears twice in code.
  const renamed = source.split(name + '(').join(name + '_renamed(');
  refuses(renamed, /scope not found/, 'missing scope');
  refuses(renamed.replace('fn ' + name + '_renamed(', '// ' + header + '\nfn ' + name + '_renamed('), /scope not found/, 'header only in a comment');
  refuses(renamed.replace('fn ' + name + '_renamed(', 'const _: &str = "' + header + '";\nfn ' + name + '_renamed('), /scope not found/, 'header only in a string');
  refuses(source.replace(header, header + ') {}\n' + header), /ambiguous mutation scope/, 'ambiguous scope');
  // Lynn's bodyless case: the only real header is a trait method declaration,
  // followed by another method whose body contains the anchor.
  const signature = source.slice(start, source.indexOf('{', start)).trim();
  refuses(renamed.replace('fn ' + name + '_renamed(',
    'trait ScopeGuardProbe {\n    ' + signature + ';\n    fn later() -> Result<(), Error> { ' + needle + ' }\n}\nfn ' + name + '_renamed('),
    /declaration ends before its body/, 'bodyless declaration');
  // A `;` inside the signature's brackets is not the end of the declaration.
  const padded = variant(body.replace(header, header + '_pad: [u8; 1], '));
  const paddedMutant = prepare(mode, padded), paddedAt = [...paddedMutant].findIndex((c, i) => c !== padded[i]);
  assert(paddedAt > start && paddedAt < end + 20, 'control array type in signature: edit stays inside the function');
  // Braces in comments and every literal form inside the function must not move
  // its end; the edit stays inside the function.
  const braces = body.replace('{', '{\n    // }\n    /* } /* { */ } */\n    let _ = "}";\n    let _ = \'}\';\n    let _ = b\'}\';\n    let _ = r#"}"#;\n    let _ = br"}";\n    let _ = c"}";\n    let _ = cr#"}"#;\n');
  const text = variant(braces), mutant = prepare(mode, text);
  const at = [...mutant].findIndex((c, i) => c !== text[i]);
  assert(at > start && at < start + braces.length, 'control braces in comments/literals: edit stays inside the function');
  // Lynn's C-raw counterexample: an opening `{` in a C raw string here and a
  // closing `}` in one inside a later item, with the local anchor spelled
  // differently, must refuse rather than edit the later item.
  const opened = variant(body.replace(needle, spelled).replace('{', '{\n    let _ = cr#"" { ""#;'));
  const shift = opened.length - source.length;
  const crossed = opened.slice(0, laterStart + shift) + opened.slice(laterStart + shift).replace('{', '{\n        let _ = cr#"" } ""#;');
  refuses(crossed, /anchor not found in its scope/, 'C raw strings across items');
  // Source the lexer cannot classify is refused, not guessed.
  refuses(variant(body.replace('{', "{\n    let _ = '\\q';\n")), /unsupported quote/, 'unclassifiable quote');
  refuses(variant(body.replace('{', '{\n    let _ = x"}";\n')), /unsupported literal prefix/, 'unknown literal prefix');
}
