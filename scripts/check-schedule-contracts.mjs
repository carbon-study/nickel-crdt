// Readiness and selection compose checked loop and membership contracts.
import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import path from 'node:path';
import {put,verify} from './proof-cache.mjs';
import {hasOrdinaryTheoremRejection} from './negative-proof-evidence.mjs';
export async function checkScheduleContracts({proof,output,fstar,models,modelCache}) {
  const name='Nickel.EditSchedule.fst', original=await fs.readFile(path.join(proof,name),'utf8');
  const controls=[
    ['schedule-available-without-choice-contract',/  scheduler_choice_is_exact facts done;\n/,'available_event_is_chosen'],
    ['schedule-ready-without-loop',/  Nickel\.LoopUtil\.preserve_any \(mk_usize 0\) \(Core_models\.Slice\.impl__len after\)[^\n]+;\n/,'readiness_is_exact'],
    ['schedule-choice-without-loop',/  Nickel\.LoopUtil\.preserve_any \(mk_usize 0\) \(Core_models\.Slice\.impl__len facts\)[^\n]+;\n/,'scheduler_choice_is_exact'],
    ['schedule-choice-without-ready-contract',/(?<=let readiness_is_exact[^\n]*) \[SMTPat \(Native\.ready after done\)\]/,'scheduler_choice_is_exact'],
  ];
  for(const [control,pattern,owner] of controls) {
    assert.equal([...original.matchAll(new RegExp(pattern.source,'g'))].length,1,control+' anchor');
    const dir=path.join(path.dirname(proof),control);await fs.rm(dir,{recursive:true,force:true});
    await fs.cp(proof,dir,{recursive:true,preserveTimestamps:true});
    const view=original.replace(pattern,'');await put(path.join(dir,name),view);
    const r=await verify({dir,roots:[path.join(dir,name)],fstar,models,modelCache});
    await fs.writeFile(path.join(output,control+'.proof.log'),r.log);
    assert(hasOrdinaryTheoremRejection({status:r.status,log:r.log,theorem:'Nickel.EditSchedule.'+owner,view}),control+': '+r.log);
    console.log('PASS '+control+': ordinary owning rejection');
  }
}
