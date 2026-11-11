// Actual text callers must require the generic algorithm contract with that
// algorithm's body withheld. These are dependency controls, not Rust mutants.
import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import path from 'node:path';
import {put,verify} from './proof-cache.mjs';
import {hasOrdinaryTheoremRejection} from './negative-proof-evidence.mjs';
export async function checkEventContracts({proof,output,fstar,models,modelCache}) {
  const cases=[
    ['duplicate','EditAtomic','plan_preserves_duplicate_result','Nickel.EventShell.planning_is_exact'],
    ['validation','EditAtomic','successful_plan_requires_validation','Nickel.EventShell.planning_is_exact'],
    ['neutral','EditAtomic','receive_rejection_unchanged','Nickel.EventShell.publication_is_exact'],
    ['receive','EditCommit','receive_uses_plan','Nickel.EventShell.publication_is_exact'],
    ['private','EditCommit','plan_preserves_private_state','Nickel.EventShell.planning_is_exact'],
    ['shared','EditCommit','plan_ignores_private_state','Nickel.EventShell.planning_is_exact'],
    ['classifier','EditIdentity','duplicate_matches_lookup','Nickel.EventClassifier.classification_is_exact'],
  ];
  for(const [label,module,owner,contract] of cases) {
    const name='event-without-'+label,file='Nickel.'+module+'.fst';
    const original=await fs.readFile(path.join(proof,file),'utf8');
    const declaration=new RegExp('^let '+owner+' ','m').exec(original);assert(declaration,name+' owner declaration');
    const start=declaration.index,next=/\nlet (?:rec )?\w+ /.exec(original.slice(start+declaration[0].length));
    const end=next?start+declaration[0].length+next.index:original.length;
    let body=original.slice(start,end);
    const needle="    Tactics.smt_sync' 1 1";assert.equal(body.split(needle).length,2,name+' unique owning query');
    body=body.replace(needle,'    Tactics.prune "'+contract+'";\n'+needle);
    if(label==='classifier') {
      const use='  Nickel.EventClassifier.classification_is_exact facts fact Native.fact_id Native.same_event_id Native.fact_equal;\n';
      assert.equal(body.split(use).length,2,name+' explicit contract use');body=body.replace(use,'');
    }
    const view=original.slice(0,start)+body+original.slice(end);
    const dir=path.join(path.dirname(proof),name);
    await fs.rm(dir,{recursive:true,force:true});await fs.cp(proof,dir,{recursive:true,preserveTimestamps:true});
    await put(path.join(dir,file),view);
    const result=await verify({dir,roots:[path.join(dir,file)],fstar,models,modelCache});
    await fs.writeFile(path.join(output,name+'.proof.log'),result.log);
    assert(hasOrdinaryTheoremRejection({status:result.status,log:result.log,theorem:'Nickel.'+module+'.'+owner,view}),name+': require the exact ordinary caller rejection: '+result.log);
    console.log('PASS '+name+': concrete caller requires '+contract);
  }
}
