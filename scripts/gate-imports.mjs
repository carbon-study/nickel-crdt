// Gate import parser (moved from check-gate-inputs.mjs for #197 so gate closures can include it): every static
// form via node's module parser (needs --experimental-vm-modules), plus literal dynamic imports; any other dynamic
// import or non-builtin specifier refuses rather than silently missing a runtime dependency. The dynamic-import
// pattern is assembled from pieces so this module's own source never looks like a dynamic import to it.
import assert from 'node:assert/strict';
import vm from 'node:vm';
import {isBuiltin} from 'node:module';
export function dependencies(source, name) {
  const specs = [...new vm.SourceTextModule(source, {identifier:name}).dependencySpecifiers];
  // Conservative: also finds apparent imports in comments/strings. Unsupported
  // forms refuse rather than silently missing a runtime dependency.
  const dynamic = new RegExp('\\bim'+'port(?:(?:\\s+)|(?:\\/\\/[^\\r\\n\\u2028\\u2029]*[\\r\\n\\u2028\\u2029])|(?:\\/\\*[\\s\\S]*?\\*\\/))*\\(','g');
  for (const m of source.matchAll(dynamic)) {
    const literal = /^\s*(['"])([^'"\\\r\n]+)\1\s*\)/.exec(source.slice(m.index+m[0].length));
    assert(literal, name+': unsupported dynamic import; use a plain literal');
    specs.push(literal[2]);
  }
  return [...new Set(specs.filter(s=>!isBuiltin(s)).map(s=>{
    assert(/^\.\/[a-z0-9-]+\.mjs$/.test(s), name+': unsupported non-builtin dependency '+s);
    return s.slice(2);
  }))].sort();
}
