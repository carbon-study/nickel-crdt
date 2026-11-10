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
    ['schedule-rank-without-induction',/no_choice_finishes_lower_ranks facts done rank bound \(finish - 1\);\n/,'no_choice_finishes_lower_ranks','no_choice_finishes_lower_ranks'],
    ['schedule-unfinished-without-ranks',/    no_choice_finishes_lower_ranks facts done rank bound bound;\n/,'ranked_unfinished_has_eligible','ranked_unfinished_has_eligible'],
    ['schedule-incomplete-without-ranks',/    no_choice_finishes_lower_ranks facts done rank bound bound;\n/,'ranked_incomplete_has_eligible','ranked_incomplete_has_eligible'],
    ['schedule-incomplete-without-count',/    shorter_done_is_unfinished input done;\n/,'ranked_incomplete_has_eligible','ranked_incomplete_has_eligible'],
    ['schedule-progress-without-existence',/  ranked_incomplete_has_eligible facts done rank bound;\n/,'ranked_incomplete_scan_progress','ranked_incomplete_scan_progress'],
    ['schedule-progress-without-choice',/  scheduler_choice_is_exact input done;\n/,'ranked_incomplete_scan_progress','ranked_incomplete_scan_progress'],
    ['schedule-count-without-collision',/FStar\.Fin\.pigeonhole positions/,'shorter_done_is_unfinished','shorter_done_is_unfinished','(0, 0)'],
  ];
  for(const [control,pattern,owner,scope,replacement=''] of controls) {
    let start=0,end=original.length;
    if(scope) {
      const declaration=new RegExp('^let (?:rec )?'+scope+' ','m').exec(original);assert(declaration,control+' declaration');
      start=declaration.index;
      const next=/\nlet (?:rec )?\w+ /.exec(original.slice(start+declaration[0].length));
      end=next?start+declaration[0].length+next.index:original.length;
    }
    const body=original.slice(start,end);
    assert.equal([...body.matchAll(new RegExp(pattern.source,'g'))].length,1,control+' anchor');
    const dir=path.join(path.dirname(proof),control);await fs.rm(dir,{recursive:true,force:true});
    await fs.cp(proof,dir,{recursive:true,preserveTimestamps:true});
    const view=original.slice(0,start)+body.replace(pattern,replacement)+original.slice(end);await put(path.join(dir,name),view);
    const r=await verify({dir,roots:[path.join(dir,name)],fstar,models,modelCache});
    await fs.writeFile(path.join(output,control+'.proof.log'),r.log);
    assert(hasOrdinaryTheoremRejection({status:r.status,log:r.log,theorem:'Nickel.EditSchedule.'+owner,view}),control+': '+r.log);
    console.log('PASS '+control+': ordinary owning rejection');
  }
}
