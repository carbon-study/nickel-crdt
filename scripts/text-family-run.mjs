// Shared enumeration/execution boundary for the text gate's contract families (#199).
// A family module exports units(read): a pure function of the positive workspace (read(name) returns a workspace
// file's text) that returns the family's complete control inventory. Export and execution call the same function:
// export-plans reads the retained workspace files, execution reads the family's actual workspace copy, and the
// exact-tuple audit compares what execution actually did with the exported plan, field for field.
import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import path from 'node:path';
import {digest,put,verify} from './proof-cache.mjs';
import {hasOrdinaryTheoremRejection} from './negative-proof-evidence.mjs';

// The positive workspace's authored views (check-edit-proofs.mjs installs exactly these) and the extraction inventory.
export const POSITIVE_VIEWS=['EditDeletePermutation','EditDeleteAnswer','EditDeleteHeap','EditDeleteComplete','PastExact','Canonical','Prelude','LoopUtil','LoopEquality','EventGraph','EventGraphText','EventShell','EventClassifier','Vector','EditAtomic','EditCommit','EditIdentity','EditAccepted','EditWellFormed','Spec','EditCausal','EditPast','EditPastTotal','EditSchedule','EditBasis','EditReplay'];
export const EXTRACTION=['Nickel_crdt.Edit.fst','Nickel_crdt.Event_layer.fst','Nickel_crdt.Event_shell.fst'];
export const viewSource=name=>name==='Canonical'?'proofs/register-view/Nickel.Canonical.fst':`proofs/generated/Nickel.${name}.fst`;
/** The retained file a positive-workspace file is installed from, or null if the workspace has no such file. */
export function retainedWorkspaceFile(file){
  if(EXTRACTION.includes(file))return 'proofs/generated/hax/'+file;
  const m=/^Nickel\.(\w+)\.fst$/.exec(file);
  return m&&POSITIVE_VIEWS.includes(m[1])?viewSource(m[1]):null;
}

/**
 * A view control: {name, files: {file: text}, roots: [file], theorem, inPlace, log, pass, failure}.
 * name is the control's PASS label; files are the workspace files it writes (each must differ from the workspace);
 * theorem is the owner whose ordinary rejection is required; inPlace runs in the family workspace itself and
 * restores it afterwards, otherwise in a fresh copy named after the control; log names the proof log in output.
 */
export function viewPlan(family,c,read){
  assert(typeof c.name==='string'&&c.name.length>0,family+': control name');
  const files=Object.keys(c.files).sort();assert(files.length>0,c.name+': a control writes at least one file');
  for(const f of files)assert.notEqual(c.files[f],read(f),c.name+': '+f+' must differ from the positive workspace');
  // expect "verify" (#198): a test-only healthy unit that must verify; it has no owner and is never a rejection.
  const expect=c.expect??'reject';assert(expect==='reject'?typeof c.theorem==='string':expect==='verify'&&c.theorem===undefined,c.name+': explicit expectation and owner');
  return {id:family+':'+c.name,kind:'family-control',family,owner:expect==='reject'?c.theorem:null,expect,roots:[...c.roots],
    mutation:files.map(file=>({file,sha256:digest(c.files[file])})),native:null};
}
export function viewUnits(family,controls,read){
  const units=controls.map(c=>({plan:viewPlan(family,c,read),control:c}));
  const ids=new Set();for(const u of units){assert(!ids.has(u.plan.id),'control listed twice: '+u.plan.id);ids.add(u.plan.id);}
  return units;
}

/** Runs view units in order. record(ran) receives what each control actually did (roots passed to the verifier, the
 *  digests of the files it wrote, the owner judged and the outcome asserted). */
export async function runViewUnits(units,{proof,output,fstar,models,modelCache},record){
  for(const {plan,control:c} of units){
    const dir=c.inPlace?proof:path.join(path.dirname(proof),c.name);
    const files=Object.keys(c.files).sort();
    const originals=c.inPlace?Object.fromEntries(await Promise.all(files.map(async f=>[f,await fs.readFile(path.join(proof,f),'utf8')]))):null;
    // Files a unit must leave untouched (e.g. the extracted native program under a ghost-only fault), checked before
    // verification and again after an in-place unit restores its workspace.
    const keep=c.unchanged??[],kept=Object.fromEntries(await Promise.all(keep.map(async f=>[f,await fs.readFile(path.join(proof,f),'utf8')])));
    const ran={id:plan.id,kind:'family-control',family:plan.family,owner:null,expect:null,roots:null,mutation:null,native:null};
    try{
      if(!c.inPlace){await fs.rm(dir,{recursive:true,force:true});await fs.cp(proof,dir,{recursive:true,preserveTimestamps:true});}
      for(const f of files)await put(path.join(dir,f),c.files[f]);
      ran.mutation=await Promise.all(files.map(async file=>({file,sha256:digest(await fs.readFile(path.join(dir,file)))})));
      for(const k of keep)assert.equal(await fs.readFile(path.join(dir,k),'utf8'),kept[k],c.name+': '+k+' must stay unchanged');
      ran.roots=[...c.roots];
      const result=await verify({dir,roots:c.roots.map(r=>path.join(dir,r)),fstar,models,modelCache});
      await fs.writeFile(path.join(output,c.log),result.log);
      if((c.expect??'reject')==='verify'){assert.equal(result.status,0,c.failure+': '+result.log);ran.expect='verify';}
      else{
        // The rejection is judged against the owner's module as verified.
        const ownerFile=c.theorem.split('.').slice(0,-1).join('.')+'.fst';
        const view=await fs.readFile(path.join(dir,ownerFile),'utf8');
        assert(hasOrdinaryTheoremRejection({status:result.status,log:result.log,theorem:c.theorem,view}),c.failure+': '+result.log);
        ran.owner=c.theorem;ran.expect='reject';
      }
    }finally{if(originals){for(const f of files)await put(path.join(proof,f),originals[f]);
      for(const f of files)assert.equal(await fs.readFile(path.join(proof,f),'utf8'),originals[f],c.name+': restore '+f+' after the unit');
      for(const k of keep)assert.equal(await fs.readFile(path.join(proof,k),'utf8'),kept[k],c.name+': '+k+' remains unchanged');}}
    record(ran);
    console.log('PASS '+c.pass);
  }
}
/** A family's plan digest: the selector records it per family, a consumer recomputes it for the families it runs. */
export const familyPlanDigest=plans=>digest(JSON.stringify(plans));
/** Audit controls on real family tuples (at least two): a hidden control, an unexecuted plan, changed roots, a wrong
 *  expectation, a different mutation digest, a different owner and different native inputs must each be refused. */
export function checkFamilyAuditControls(auditUnits,plans){
  assert(plans.length>=2,'family audit controls need two family tuples');
  const two=plans.slice(0,2),copy=x=>structuredClone(x);
  assert.equal(auditUnits(two,two.map(copy)),2);
  assert.throws(()=>auditUnits(two,[...two.map(copy),{...copy(two[0]),id:two[0].id+'-hidden'}]),/hidden unit executed without a plan/,'hidden control');
  assert.throws(()=>auditUnits(two,two.slice(1).map(copy)),/planned unit not executed/,'unexecuted plan');
  const tweak=f=>{const ran=two.map(copy);f(ran[1]);return ran;};
  for(const [what,f] of [['changed roots',u=>{u.roots=[...u.roots,'Nickel.EditAtomic.fst'];}],['wrong expectation',u=>{u.expect=u.expect==='reject'?'verify':'reject';}],
    ['mutation digest',u=>{u.mutation[0].sha256='0'.repeat(64);}],['owner',u=>{u.owner=(u.owner??'Nickel.X.y')+'_other';}],['native inputs',u=>{u.native=u.native?null:{cargoArgs:['test'],baselines:[],extraction:true};}]])
    assert.throws(()=>auditUnits(two,tweak(f)),/executed unit differs from its plan/,what);
}
/** Audit controls for explicit expect "verify" units (#198), on real tuples: for each such unit, an execution that runs
 *  it while the plan omits it (a hidden healthy unit), or that records it as a rejection or with an owner (a wrong
 *  expectation), must be refused. Returns how many verify units were exercised. */
export function checkVerifyUnitAuditControls(auditUnits,plans){
  const verifyUnits=plans.filter(p=>p.expect==='verify');
  const copy=x=>structuredClone(x);
  for(const v of verifyUnits){
    const others=plans.filter(p=>p.id!==v.id);
    assert.throws(()=>auditUnits(others,plans.map(copy)),/hidden unit executed without a plan/,'hidden verify unit '+v.id);
    const wrong=plans.map(p=>p.id===v.id?{...copy(p),expect:'reject'}:copy(p));
    assert.throws(()=>auditUnits(plans,wrong),/executed unit differs from its plan/,'wrong expectation '+v.id);
    const owned=plans.map(p=>p.id===v.id?{...copy(p),owner:'Nickel.EditAccepted.canonical_succeeds_for_unique_ids'}:copy(p));
    assert.throws(()=>auditUnits(plans,owned),/executed unit differs from its plan/,'owner on a verify unit '+v.id);
  }
  return verifyUnits.length;
}
