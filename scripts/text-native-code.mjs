// The text gate's native-path code inputs (#197): check-edit-proofs.mjs plus everything it loads by a literal import
// (every static form and literal dynamic imports, parsed by check-gate-inputs' own parser; anything else refuses),
// transitively, except the one named module text-families.mjs, which the runner loads only for families,
// cache-safety or gatepreflight. Shared by the selector (at base and head) and the selection consumer (its own tree).
import assert from 'node:assert/strict';
import {dependencies} from './gate-imports.mjs';
export const TEXT_RUNNER='check-edit-proofs.mjs',TEXT_FAMILIES='text-families.mjs';
/** read(name) returns the module source, or null if absent. Returns the sorted script names (without "scripts/"). */
export async function nativeCodeClosure(read){
  const seen=new Set(),stack=[TEXT_RUNNER];
  while(stack.length){
    const f=stack.pop();if(seen.has(f)||f===TEXT_FAMILIES)continue;
    const text=await read(f);if(text===null)throw new Error('native code input unreadable: '+f);
    seen.add(f);for(const d of dependencies(text,f))stack.push(d);
  }
  return [...seen].sort();
}
/** A record's native-code entries must be exactly this tree's closure, each with this tree's digest. */
export function checkNativeCodeRecord(recorded,closure,digestOf){
  assert(recorded&&typeof recorded==='object'&&!Array.isArray(recorded),'selection record native code set');
  const want=closure.map(f=>'scripts/'+f).sort(),got=Object.keys(recorded).sort();
  const missing=want.filter(f=>!got.includes(f)),extra=got.filter(f=>!want.includes(f));
  assert.deepEqual([missing,extra],[[],[]],'selection record native code set differs from this tree\'s closure (missing: '+missing.join(',')+'; extra: '+extra.join(',')+')');
  for(const f of want){assert(/^[0-9a-f]{64}$/.test(recorded[f]??''),'malformed native code digest '+f);
    assert.equal(digestOf(f),recorded[f],'selection record was not made for this tree (native code differs: '+f+')');}
}
/** Controls: complete set accepted; an omitted static helper, an extra entry and a wrong digest each refused. */
export function checkNativeCodeControls(){
  const closure=['check-edit-proofs.mjs','proof-cache.mjs','mutation-scope.mjs'],d=f=>f.length.toString(16).padStart(64,'0');
  const rec=Object.fromEntries(closure.map(f=>['scripts/'+f,d('scripts/'+f)]));
  checkNativeCodeRecord(rec,closure,d);
  const {['scripts/proof-cache.mjs']:_,...omitted}=rec;
  assert.throws(()=>checkNativeCodeRecord(omitted,closure,d),/missing: scripts\/proof-cache\.mjs/,'omitted static helper');
  assert.throws(()=>checkNativeCodeRecord({...rec,'scripts/extra.mjs':d('x')},closure,d),/extra: scripts\/extra\.mjs/,'extra entry');
  assert.throws(()=>checkNativeCodeRecord({...rec,'scripts/proof-cache.mjs':'0'.repeat(64)},closure,d),/native code differs: scripts\/proof-cache\.mjs/,'wrong digest');
  assert.throws(()=>checkNativeCodeRecord({'scripts/check-edit-proofs.mjs':rec['scripts/check-edit-proofs.mjs']},closure,d),/missing: /,'runner-only set (the reviewed counterexample)');
}

/** Head-input binding: recorded maps path -> digest at the selector's head; present lists this tree's files under the
 *  selection-relevant roots; declared lists the packaged paths (files or directories). Every present file must be
 *  recorded with its digest (change or addition refuses); every recorded declared file must be present (deletion
 *  refuses); recorded files outside the declaration may be absent. Returns how many recorded files are undeclared. */
export function checkHeadInputs(recorded,present,digestOf,declared){
  assert(recorded&&typeof recorded==='object'&&!Array.isArray(recorded),'selection record head inputs');
  for(const f of present){assert(Object.hasOwn(recorded,f),'selection record was not made for this tree (unrecorded input '+f+')');
    assert.equal(digestOf(f),recorded[f],'selection record was not made for this tree (input differs: '+f+')');}
  const packaged=f=>declared.some(p=>f===p||f.startsWith(p+'/'));
  const have=new Set(present),missing=Object.keys(recorded).filter(f=>packaged(f)&&!have.has(f));
  assert.deepEqual(missing,[],'selection record was not made for this tree (declared packaged input missing: '+missing.join(', ')+')');
  return Object.keys(recorded).filter(f=>!packaged(f)).length;
}
export function checkHeadInputControls(){
  const d=f=>'d'.repeat(63)+String(f.length%10);
  const rec={'proofs/generated/A.fst':d('proofs/generated/A.fst'),'proofs/generated/hax/B.fst':d('proofs/generated/hax/B.fst'),'scripts/x.mjs':d('scripts/x.mjs'),'proofs/register-view/R.fst':d('proofs/register-view/R.fst'),'nix/text-inputs.json':d('nix/text-inputs.json')};
  const declared=['proofs/generated','scripts/x.mjs','nix/text-inputs.json'];
  const full=['proofs/generated/A.fst','proofs/generated/hax/B.fst','scripts/x.mjs','nix/text-inputs.json'];
  assert.equal(checkHeadInputs(rec,full,d,declared),1,'undeclared recorded file counted');
  assert.throws(()=>checkHeadInputs(rec,[...full,'proofs/generated/C.fst'],d,declared),/unrecorded input proofs\/generated\/C\.fst/,'added input');
  assert.throws(()=>checkHeadInputs(rec,full,f=>f==='scripts/x.mjs'?'0'.repeat(64):d(f),declared),/input differs: scripts\/x\.mjs/,'changed input');
  assert.throws(()=>checkHeadInputs(rec,full.filter(f=>f!=='proofs/generated/hax/B.fst'),d,declared),/declared packaged input missing: proofs\/generated\/hax\/B\.fst/,'deleted declared file in a declared directory');
  assert.throws(()=>checkHeadInputs(rec,full.filter(f=>f!=='scripts/x.mjs'),d,declared),/declared packaged input missing: scripts\/x\.mjs/,'deleted declared file');
  assert.equal(checkHeadInputs(rec,full,d,declared),1,'an undeclared recorded file may be absent');
  assert.throws(()=>checkHeadInputs(rec,full,f=>f==='nix/text-inputs.json'?'0'.repeat(64):d(f),declared.filter(p=>p!=='scripts/x.mjs')),/input differs: nix\/text-inputs\.json/,'a deletion hidden by editing the declaration');
}
