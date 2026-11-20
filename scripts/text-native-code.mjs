// The text gate's native-path code inputs (#197): check-edit-proofs.mjs plus everything it loads by a literal import
// (every static form and literal dynamic imports, parsed by check-gate-inputs' own parser; anything else refuses),
// transitively, except the one named module text-families.mjs, which the runner loads only for families,
// cache-safety or gatepreflight. Shared by the selector (at base and head) and the selection consumer (its own tree).
import assert from 'node:assert/strict';
import {dependencies} from './gate-imports.mjs';
import {UNIT_GROUPS,UNIT_MODULES} from './text-unit-groups.mjs';
import {readFileSync as readFileSyncTI} from 'node:fs';
import {lstat as lstatTI,readdir as readdirTI} from 'node:fs/promises';
import {join as joinTI} from 'node:path';
import {createHash as createHashTI} from 'node:crypto';
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

// ---------------------------------------------------------------- family code inputs (#199)
/** A family's code: its module plus everything that module loads by a literal import, transitively (the same parser).
 *  read(name) returns a script's source or null. Returns sorted script names (without "scripts/"). */
export async function familyCodeClosure(read,module){
  const seen=new Set(),stack=[module];
  while(stack.length){
    const f=stack.pop();if(seen.has(f))continue;
    const text=await read(f);if(text===null)throw new Error('family code input unreadable: '+f);
    seen.add(f);for(const d of dependencies(text,f))stack.push(d);
  }
  return [...seen].sort();
}
/** A record's family code must name exactly this tree's converted families, each with exactly this tree's closure and
 *  digests. closures maps family -> sorted script names. */
export function checkFamilyCodeRecord(recorded,closures,digestOf){
  assert(recorded&&typeof recorded==='object'&&!Array.isArray(recorded),'selection record family code');
  assert.deepEqual(Object.keys(recorded).sort(),Object.keys(closures).sort(),'selection record family code names other families than this tree converts');
  for(const [family,names] of Object.entries(closures)){
    const r=recorded[family];assert(r&&typeof r==='object'&&!Array.isArray(r),'selection record family code '+family);
    const want=names.map(f=>'scripts/'+f).sort(),got=Object.keys(r).sort();
    const missing=want.filter(f=>!got.includes(f)),extra=got.filter(f=>!want.includes(f));
    assert.deepEqual([missing,extra],[[],[]],'selection record code of family '+family+' differs from this tree\'s closure (missing: '+missing.join(',')+'; extra: '+extra.join(',')+')');
    for(const f of want){assert(/^[0-9a-f]{64}$/.test(r[f]??''),'malformed family code digest '+f);
      assert.equal(digestOf(f),r[f],'selection record was not made for this tree (code of family '+family+' differs: '+f+')');}
  }
}
export function checkFamilyCodeControls(){
  const d=f=>f.length.toString(16).padStart(64,'0');
  const closures={past:['check-past-contracts.mjs','text-family-run.mjs'],delete:['check-delete-contracts.mjs','delete-control-fixtures.mjs']};
  const rec=Object.fromEntries(Object.entries(closures).map(([k,v])=>[k,Object.fromEntries(v.map(f=>['scripts/'+f,d('scripts/'+f)]))]));
  checkFamilyCodeRecord(rec,closures,d);
  const {['scripts/delete-control-fixtures.mjs']:_,...short}=rec.delete;
  assert.throws(()=>checkFamilyCodeRecord({...rec,delete:short},closures,d),/missing: scripts\/delete-control-fixtures\.mjs/,'omitted family helper');
  assert.throws(()=>checkFamilyCodeRecord({...rec,past:{...rec.past,'scripts/x.mjs':d('x')}},closures,d),/extra: scripts\/x\.mjs/,'extra family entry');
  assert.throws(()=>checkFamilyCodeRecord({...rec,past:{...rec.past,'scripts/check-past-contracts.mjs':'0'.repeat(64)}},closures,d),/code of family past differs/,'wrong family digest');
  const {past:__,...onlyDelete}=rec;
  assert.throws(()=>checkFamilyCodeRecord(onlyDelete,closures,d),/other families/,'a family left out of the record');
}

// ---------------------------------------------------------------- shared record binding (#198)
/** The roots of the files a text decision depends on (the selector records every head file under them). */
export const TEXT_INPUT_ROOTS=['proofs','src','tests','proof-smoke','scripts','Cargo.toml','Cargo.lock','nix/text-inputs.json','nix/gate-scripts.json'];
const fileDigest=(root,f)=>createHashTI('sha256').update(readFileSyncTI(joinTI(root,f))).digest('hex');
/** Binds a record's headInputs to this tree: every present file under the roots recorded with its digest, every
 *  recorded declared packaged input present. Returns how many recorded files are undeclared. */
export async function bindHeadInputs(root,headInputs){
  assert(headInputs&&typeof headInputs==='object'&&!Array.isArray(headInputs),'selection record head inputs');
  const present=[];const walk=async rel=>{let st;try{st=await lstatTI(joinTI(root,rel));}catch{return;}
    if(st.isDirectory()){for(const e of (await readdirTI(joinTI(root,rel))).sort())await walk(rel+'/'+e);}else if(st.isFile())present.push(rel);};
  for(const r of TEXT_INPUT_ROOTS)await walk(r);
  const decl=JSON.parse(readFileSyncTI(joinTI(root,'nix/text-inputs.json'),'utf8')),gates=JSON.parse(readFileSyncTI(joinTI(root,'nix/gate-scripts.json'),'utf8'));
  assert(Array.isArray(decl.paths)&&decl.paths.every(p=>typeof p==='string')&&Array.isArray(gates.text),'packaged input declarations');
  const undeclared=checkHeadInputs(headInputs,present,f=>fileDigest(root,f),[...decl.paths,...gates.text.map(n=>'scripts/'+n)]);
  return {present:present.length,undeclared};
}
/** The smoke gate's selection decision (#198). The record must be a non-diagnostic text record; a full text or unit-group
 *  route runs smoke. Otherwise it is bound to this tree's inputs, every unit group's code closure and the smoke plan
 *  digest (computed by the caller from this tree), and smoke runs iff it is selected. */
export async function checkSmokeSelection(root,file,smokeDigest){
  let rec;try{rec=JSON.parse(readFileSyncTI(file,'utf8'));}catch(e){assert.fail('selection record unreadable: '+e.message);}
  const keys=['schema','base','head','diagnosticOnly','basePlans','headPlans','full','reasons','affected','register','text','shared'];
  assert(rec&&typeof rec==='object'&&!Array.isArray(rec)&&Object.keys(rec).length===keys.length&&keys.every(k=>Object.hasOwn(rec,k)),'selection record has an unrecognised shape');
  assert.equal(rec.schema,1,'selection record schema');assert.equal(rec.diagnosticOnly,false,'a diagnostic selection record cannot be consumed');
  const t=rec.text;assert(t&&typeof t==='object'&&!Array.isArray(t),'selection record text entry');
  if(rec.full===true||t.run==='full'){assert.deepEqual(Object.keys(t),['run'],'a full text selection carries only run');assert.equal(t.run,'full');return {run:true,why:'full text route'};}
  const f=t.families;assert(f&&typeof f==='object'&&!Array.isArray(f),'selection record family entry');
  if(f.run==='full'){assert.deepEqual(Object.keys(f),['run'],'a full family selection carries only run');return {run:true,why:'full unit-group route'};}
  const fkeys=['run','selected','why','removed','total','headPlans','basePlans','digests','familyCode'];
  assert(Object.keys(f).length===fkeys.length&&fkeys.every(k=>Object.hasOwn(f,k)),'selection record family entry has an unrecognised shape');
  const bound=await bindHeadInputs(root,t.headInputs);
  const readScript=async n=>{try{return readFileSyncTI(joinTI(root,'scripts',n),'utf8');}catch{return null;}};
  const closures={};for(const n of UNIT_GROUPS)closures[n]=await familyCodeClosure(readScript,UNIT_MODULES[n]);
  checkFamilyCodeRecord(f.familyCode,closures,p=>fileDigest(root,p));
  assert(Array.isArray(f.selected)&&f.selected.every(n=>UNIT_GROUPS.includes(n))&&new Set(f.selected).size===f.selected.length,'selection names unknown or repeated unit groups');
  assert(f.run==='selected'?f.selected.length>0:f.run==='none'&&f.selected.length===0,'family selection run and families agree');
  assert(f.digests&&typeof f.digests==='object'&&Object.keys(f.digests).sort().join()===[...UNIT_GROUPS].sort().join(),'selection record unit-group plan digests');
  assert.equal(smokeDigest,f.digests.smoke,'selection record was not made for this tree (smoke plans differ)');
  const run=f.selected.includes('smoke');
  return {run,why:(run?'selected ('+f.why.smoke+')':'not selected')+'; '+bound.present+' files of this tree bound to the record'};
}
