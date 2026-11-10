// Fail-closed mutation scoping for the Rust source under proof.
//
// A mutation names an item header (for example `fn plan(`) and an exact anchor
// string. The anchor must occur exactly once inside that item's brace-matched
// body; otherwise preparation refuses. The body is found by a small lexer that
// skips comments and string, char, byte and raw-string literals, so braces
// inside them cannot move the boundary. Source the lexer cannot classify is
// refused rather than guessed. The guarantee is narrow: exactly one edit inside
// the intended item. Whether that edit is still the named semantic fault is a
// review obligation.
import assert from 'node:assert/strict';

const ident = c => c !== undefined && /[A-Za-z0-9_]/.test(c);
const CHAR = /^'(?:[^'\\\n]|\\(?:[nrt\\0'"]|x[0-9a-fA-F]{2}|u\{[0-9a-fA-F]{1,6}\}))'/;
const LIFETIME = /^'[A-Za-z_][A-Za-z0-9_]*/;

// Index of the first non-code-skipping step at or after `i`: returns the index
// just past a comment or literal starting at `i`, or `i` itself for code.
function skip(source, i, where) {
  const rest = source.slice(i, i + 2);
  if (rest === '//') { const nl = source.indexOf('\n', i); return nl < 0 ? source.length : nl; }
  if (rest === '/*') {
    let depth = 0, j = i;
    while (j < source.length) {
      if (source.startsWith('/*', j)) { depth++; j += 2; }
      else if (source.startsWith('*/', j)) { depth--; j += 2; if (depth === 0) return j; }
      else j++;
    }
    throw new Error(`${where}: unterminated block comment`);
  }
  const c = source[i];
  if ((c === 'r' || c === 'b') && !ident(source[i - 1])) {
    const raw = /^b?r(#*)"/.exec(source.slice(i, i + 260));
    if (raw) {
      const close = '"' + raw[1], end = source.indexOf(close, i + raw[0].length);
      if (end < 0) throw new Error(`${where}: unterminated raw string`);
      return end + close.length;
    }
    if (c === 'b' && (source[i + 1] === '"' || source[i + 1] === "'")) return skip(source, i + 1, where);
  }
  if (c === '"') {
    for (let j = i + 1; j < source.length; j++) {
      if (source[j] === '\\') j++;
      else if (source[j] === '"') return j + 1;
    }
    throw new Error(`${where}: unterminated string literal`);
  }
  if (c === "'") {
    const tail = source.slice(i, i + 12);
    const ch = CHAR.exec(tail); if (ch) return i + ch[0].length;
    const life = LIFETIME.exec(tail); if (life && source[i + life[0].length] !== "'") return i + life[0].length;
    throw new Error(`${where}: unsupported quote at offset ${i}`);
  }
  return i;
}

// [start, end) of the item whose header occurs exactly once in `source`.
export function itemSpan(source, header, where = header) {
  const first = source.indexOf(header);
  assert(first >= 0, `${where}: mutation scope not found: ${header}`);
  assert.equal(source.indexOf(header, first + 1), -1, `${where}: ambiguous mutation scope: ${header}`);
  let depth = 0;
  for (let i = first; i < source.length;) {
    const next = skip(source, i, where);
    if (next !== i) { i = next; continue; }
    if (source[i] === '{') depth++;
    else if (source[i] === '}') { depth--; assert(depth >= 0, `${where}: unbalanced braces in scope`); if (depth === 0) return [first, i + 1]; }
    i++;
  }
  throw new Error(`${where}: mutation scope has no complete body: ${header}`);
}

// Offset of the single anchor occurrence inside the named item.
export function scopedAnchor(source, header, needle, where) {
  const [start, end] = itemSpan(source, header, where);
  const body = source.slice(start, end), at = body.indexOf(needle);
  assert(at >= 0, `${where}: mutation anchor not found in its scope`);
  assert.equal(body.indexOf(needle, at + 1), -1, `${where}: mutation anchor is ambiguous in its scope`);
  return start + at;
}

// Controls through the caller's actual preparation path. `prepare(mode, source)`
// must return the mutated source or throw. They build variants of the real file.
export function checkMutationScopeControls(prepare, source, mode, header, needle) {
  const [start, end] = itemSpan(source, header, 'control');
  const body = source.slice(start, end);
  assert.equal(body.split(needle).length, 2, 'control precondition: one anchor in the control scope');
  assert(source.split(needle).length > 2, 'control precondition: the anchor text also occurs outside its scope');
  const variant = replacement => source.slice(0, start) + replacement + source.slice(end);
  const refuses = (text, pattern, label) =>
    assert.throws(() => prepare(mode, text), pattern, `control ${label}: preparation must refuse`);
  // The anchor leaves its function but survives elsewhere: must not silently move.
  refuses(variant(body.replace(needle, needle.replace('(', '( '))), /anchor not found in its scope/, 'moved anchor');
  // A second copy inside the function: ambiguous.
  refuses(variant(body.replace('{', '{\n    // ' + needle + '\n')), /anchor is ambiguous/, 'duplicate anchor');
  // The function is renamed away, or its header appears twice.
  refuses(variant(body.replace(header, header.replace('(', '_renamed('))), /scope not found/, 'missing scope');
  refuses(source + '\n// ' + header + '\n', /ambiguous mutation scope/, 'ambiguous scope');
  // Braces in comments and literals inside the function must not move its end.
  const braces = body.replace('{', '{\n    // }\n    /* } { */\n    let _ = "}";\n    let _ = \'}\';\n    let _ = r#"}"#;\n');
  const mutant = prepare(mode, variant(braces)), at = [...mutant].findIndex((c, i) => c !== variant(braces)[i]);
  assert(at > start && at < start + braces.length, 'control braces in comments/literals: edit stays inside the function');
  // A quote the lexer cannot classify is refused, not guessed.
  refuses(variant(body.replace('{', "{\n    let _ = '\\q';\n")), /unsupported quote/, 'unsupported source');
}
