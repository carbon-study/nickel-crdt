// Complete helper-produced operation replay and its public erasure boundary.
import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import path from 'node:path';
import {put,verify} from './proof-cache.mjs';
import {hasOrdinaryTheoremRejection} from './negative-proof-evidence.mjs';
export async function checkOperationContracts({proof,output,fstar,models,modelCache}) {
  const name='Nickel.EditSchedule.fst', original=await fs.readFile(path.join(proof,name),'utf8');
  const controls=[
    ['operation-success-without-loop',/  Nickel\.LoopUtil\.result_preserve_any [^\n]+;\n/,'successful_schedule_has_complete_event_work','successful_schedule_has_complete_event_work'],
    ['operation-success-without-empty',/  prefix_starts_at_actual_empty facts;\n/,'successful_schedule_has_complete_event_work','successful_schedule_has_complete_event_work'],
    ['operation-success-without-extension',/    prefix_extension_is_actual_work facts [^\n]+;\n/,'successful_schedule_has_complete_event_work','successful_schedule_has_complete_event_work'],
    ['operation-labels-without-induction',/actual_prefix_groups_match_trace facts \(count - 1\) previous_done previous_operations previous_tree;/,'actual_prefix_groups_match_trace','actual_prefix_groups_match_trace','();'],
    ['operation-public-without-outer',/  successful_schedule_has_complete_event_work facts;\n/,'successful_interpretation_has_operation_provenance','successful_interpretation_has_operation_provenance'],
    ['operation-public-without-erasure',/  interpret_erases_only_schedule facts;\n/,'successful_interpretation_has_operation_provenance','successful_interpretation_has_operation_provenance'],
    ['operation-public-without-coverage',/    full_trace_covers_storage facts done;\n/,'successful_interpretation_has_operation_provenance','successful_interpretation_has_operation_provenance'],
    ['operation-public-without-labels',/    actual_prefix_groups_match_trace facts \(Seq\.length facts\) done operations tree;\n/,'successful_interpretation_has_operation_provenance','successful_interpretation_has_operation_provenance'],
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
