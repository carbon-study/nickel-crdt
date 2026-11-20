// Cache-reuse safety for seeded workspaces: a copy of the verified positive
// workspace must reuse exactly what is unchanged and recheck everything else.
import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import path from 'node:path';
import {digest,put,verify} from './proof-cache.mjs';

const probe='\n(* cache-safety probe: content change only *)\n';
// Units (#198): each case is an explicit expect "verify" tuple whose checks name the modules that must be recompiled and
// those that must be reused (and, for changed-options, the changed module budget). Export and execution share them.
const ROOT='Nickel.EditIdentity.fst';
const cases=[
    // Unchanged copy: nothing to compile.
    {name:'unchanged',edit:null,compiled:[],reused:['Nickel.Prelude.fst','Nickel.LoopUtil.fst','Nickel_crdt.Edit.fst','Nickel.EditAtomic.fst','Nickel.EditCommit.fst','Nickel.EditIdentity.fst']},
    // Changed extraction: it and every dependent recheck; independent helpers are reused.
    {name:'changed-extraction',edit:'Nickel_crdt.Edit.fst',compiled:['Nickel_crdt.Edit.fst','Nickel.EditAtomic.fst','Nickel.EditCommit.fst','Nickel.EditIdentity.fst'],reused:['Nickel.Prelude.fst','Nickel.LoopUtil.fst']},
    // Changed reusable helper: it and its dependents recheck; unrelated modules are reused.
    {name:'changed-helper',edit:'Nickel.LoopUtil.fst',compiled:['Nickel.LoopUtil.fst','Nickel.EditIdentity.fst'],reused:['Nickel.Prelude.fst','Nickel_crdt.Edit.fst','Nickel.EditAtomic.fst','Nickel.EditCommit.fst']},
    // Changed recorded options (here the per-module budget): no checked result may be reused.
    {name:'changed-options',edit:null,moduleSeconds:59,compiled:['Nickel.Prelude.fst','Nickel.LoopUtil.fst','Nickel_crdt.Edit.fst','Nickel.EditAtomic.fst','Nickel.EditCommit.fst','Nickel.EditIdentity.fst'],reused:[]},
];
export function cacheSafetyUnits(read){
  return cases.map(test=>{
    const text=test.edit?read(test.edit)+probe:null;
    return {plan:{id:'cache-safety:'+test.name,kind:'cache-safety',family:'cache-safety',owner:null,expect:'verify',roots:[ROOT],
      mutation:test.edit?[{file:test.edit,sha256:digest(text)}]:[],native:null,
      checks:{moduleSeconds:test.moduleSeconds??null,compiled:[...test.compiled],reused:[...test.reused]}},test,text};
  });
}
/** Runs cache-safety units on copies of the verified positive workspace; record(ran) receives what each actually did. */
export async function runCacheSafetyUnits(units,{positiveProof,workRoot,output,fstar,models,modelCache},record) {
  for(const {plan,test,text} of units) {
    const dir=path.join(workRoot,'cache-safety-'+test.name,'proof');
    const ran={id:plan.id,kind:'cache-safety',family:'cache-safety',owner:null,expect:null,roots:null,mutation:[],native:null,checks:null};
    await fs.rm(dir,{recursive:true,force:true});
    await fs.cp(positiveProof,dir,{recursive:true,preserveTimestamps:true});
    if(test.edit){await put(path.join(dir,test.edit),text);ran.mutation=[{file:test.edit,sha256:digest(await fs.readFile(path.join(dir,test.edit)))}];}
    ran.roots=[ROOT];
    const result=await verify({dir,roots:[path.join(dir,ROOT)],fstar,models,modelCache,...(test.moduleSeconds?{moduleSeconds:test.moduleSeconds}:{})});
    await fs.writeFile(path.join(output,'cache-safety-'+test.name+'.proof.log'),result.log);
    assert.equal(result.status,0,'cache-safety '+test.name+' must verify: '+result.log);ran.expect='verify';
    for(const name of test.compiled)assert(result.modules.includes(name),`cache-safety ${test.name}: ${name} must be rechecked; compiled ${result.modules.join(',')||'nothing'}`);
    for(const name of test.reused)assert(!result.modules.includes(name),`cache-safety ${test.name}: ${name} must be reused; compiled ${result.modules.join(',')}`);
    ran.checks={moduleSeconds:test.moduleSeconds??null,compiled:[...test.compiled],reused:[...test.reused]};
    record(ran);
    console.log(`PASS cache-safety-${test.name}: compiled ${result.modules.join(',')||'nothing'}`);
  }
}
