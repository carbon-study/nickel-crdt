// Readiness and selection compose checked loop and membership contracts.
import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import path from 'node:path';
import {put,verify} from './proof-cache.mjs';
import {hasOrdinaryTheoremRejection} from './negative-proof-evidence.mjs';
export async function checkScheduleContracts({proof,output,fstar,models,modelCache}) {
  const controls=[
    ['schedule-available-without-choice-contract',/  scheduler_choice_is_exact facts done;\n/,'available_event_is_chosen'],
    ['schedule-ready-without-generic-contract',/  Graph\.readiness_is_exact [^\n]+;\n/,'readiness_is_exact','readiness_is_exact'],
    ['schedule-ready-without-concrete-bridge',/  assert \(Shared\.ready [^\n]+;\n/,'readiness_is_exact','readiness_is_exact'],
    ['schedule-choice-without-concrete-bridge',/  assert \(Shared\.choose_ready [^\n]+;\n/,'scheduler_choice_is_exact','scheduler_choice_is_exact'],
    ['schedule-choice-without-generic-contract',/  Graph\.scheduler_choice_is_exact [^\n]+;\n/,'scheduler_choice_is_exact','scheduler_choice_is_exact'],
    ['schedule-rank-without-induction',/no_choice_finishes_lower_ranks facts done rank bound \(finish - 1\);\n/,'no_choice_finishes_lower_ranks','no_choice_finishes_lower_ranks'],
    ['schedule-unfinished-without-ranks',/    no_choice_finishes_lower_ranks facts done rank bound bound;\n/,'ranked_unfinished_has_eligible','ranked_unfinished_has_eligible'],
    ['schedule-incomplete-without-ranks',/    no_choice_finishes_lower_ranks facts done rank bound bound;\n/,'ranked_incomplete_has_eligible','ranked_incomplete_has_eligible'],
    ['schedule-incomplete-without-count',/    shorter_done_is_unfinished input done;\n/,'ranked_incomplete_has_eligible','ranked_incomplete_has_eligible'],
    ['schedule-progress-without-existence',/  ranked_incomplete_has_eligible facts done rank bound;\n/,'ranked_incomplete_scan_progress','ranked_incomplete_scan_progress'],
    ['schedule-progress-without-choice',/  scheduler_choice_is_exact input done;\n/,'ranked_incomplete_scan_progress','ranked_incomplete_scan_progress'],
    ['schedule-count-without-collision',/FStar\.Fin\.pigeonhole positions/,'shorter_done_is_unfinished','shorter_done_is_unfinished','(0, 0)'],
    ['schedule-outer-without-loop',/  Nickel\.LoopUtil\.result_preserve_any [^\n]+;\n/,'successful_schedule_is_once_only_and_causal','successful_schedule_is_once_only_and_causal'],
    ['schedule-outer-without-choice-trace',/ \[SMTPat \(Native\.choose_ready facts before\)\]/,'successful_schedule_is_once_only_and_causal','chosen_append_keeps_trace'],
    ['schedule-trace-without-choice',/  scheduler_choice_is_exact facts before;\n/,'chosen_append_keeps_trace','chosen_append_keeps_trace'],
    ['schedule-public-without-outer',/  successful_schedule_is_once_only_and_causal facts;\n/,'successful_interpretation_has_causal_schedule','successful_interpretation_has_causal_schedule'],
    ['schedule-public-without-erasure',/  interpret_erases_only_schedule facts;\n/,'successful_interpretation_has_causal_schedule','successful_interpretation_has_causal_schedule'],
    ['schedule-public-without-coverage',/full_trace_covers_storage facts done;\n/,'successful_interpretation_has_causal_schedule','successful_interpretation_has_causal_schedule'],
    ['schedule-full-without-capacity',/missing_stored_id_leaves_room stored done id;\n/,'full_trace_covers_storage','full_trace_covers_storage'],
    ['cut-final-without-past',/  scanned_roots_compute_exact_past facts roots;\n/,'successful_execution_orders_its_exact_past_cut','successful_execution_orders_its_exact_past_cut'],
    ['cut-final-without-execution',/  successful_interpretation_has_causal_schedule \(Alloc\.Vec\.impl_1__as_slice facts\) tree;\n/,'successful_execution_orders_its_exact_past_cut','successful_execution_orders_its_exact_past_cut'],
    ['cut-final-without-order',/    full_execution_orders_exact_cut facts roots selected done;\n/,'successful_execution_orders_its_exact_past_cut','successful_execution_orders_its_exact_past_cut'],
    ['cut-closed-without-edge-law',/    ancestor_follows_edge facts roots fact\.f_id id;\n/,'exact_cut_keeps_dependencies','exact_cut_keeps_dependencies'],
    ['error-origin-without-progress',/ranked_incomplete_scan_progress facts done rank bound/,'ranked_outer_errors_come_from_tree_work','ranked_outer_errors_come_from_tree_work','()'],
    ['error-origin-without-eligibility',/scheduler_choice_is_exact input done/,'ranked_outer_errors_come_from_tree_work','ranked_outer_errors_come_from_tree_work','()'],
    ['error-origin-without-operation-count',/Seq\.length \(Alloc\.Vec\.impl_1__as_slice operations\) == at/,'ranked_outer_errors_come_from_tree_work','schedule_progress_invariant','Prims.l_True'],
    ['error-origin-without-loop',/  Nickel\.LoopUtil\.result_preserve_any [^\n]+;\n/,'ranked_outer_errors_come_from_tree_work','ranked_outer_errors_come_from_tree_work'],
    ['error-public-without-origin',/  ranked_outer_errors_come_from_tree_work facts rank bound;\n/,'interpret_errors_come_from_tree_work','interpret_errors_come_from_tree_work'],
    ['error-public-without-erasure',/  interpret_erases_only_schedule \(Alloc\.Vec\.impl_1__as_slice facts\);\n/,'interpret_errors_come_from_tree_work','interpret_errors_come_from_tree_work'],
    ['error-prefix-without-empty',/  prefix_starts_at_actual_empty input;\n/,'ranked_outer_errors_come_from_tree_work','ranked_outer_errors_come_from_tree_work'],
    ['error-prefix-without-extension',/    prefix_extension_is_actual_work input \(Seq\.length \(Alloc\.Vec\.impl_1__as_slice done\)\) done operations tree index;\n/,'ranked_outer_errors_come_from_tree_work','ranked_outer_errors_come_from_tree_work'],
  ];
  // Migration map: EditSchedule.{readiness,scheduler_choice}_is_exact's
  // loop rules now belong to EventGraph. The concrete controls above remove
  // the generic callee with native bodies withheld by the caller's prunes.
  // choose_ready itself uses EventGraph.readiness, so remove that pattern at
  // its generic owner, not the now-unused concrete wrapper's pattern.
  controls.push(
    ['schedule-ready-without-loop',/  Nickel\.LoopUtil\.preserve_any [^\n]+;\n/,'readiness_is_exact','readiness_is_exact','','EventGraph'],
    ['schedule-choice-without-loop',/  Nickel\.LoopUtil\.preserve_any [^\n]+;\n/,'scheduler_choice_is_exact','scheduler_choice_is_exact','','EventGraph'],
    ['schedule-choice-without-ready-contract',/(?<=let readiness_is_exact[^\n]*) \[SMTPat \(Native\.ready after done ops\)\]/,'scheduler_choice_is_exact',undefined,'','EventGraph']
  );
  for(const [control,pattern,owner,scope,replacement='',module='EditSchedule'] of controls) {
    const name='Nickel.'+module+'.fst', original=await fs.readFile(path.join(proof,name),'utf8');
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
    let changed=body.replace(pattern,replacement);
    if(control==='schedule-ready-without-generic-contract') {
      // The generic callee also has a global SMT pattern: withhold that
      // automatic route, as well as its explicit call, in this caller.
      const anchor='    Tactics.prune "Nickel_crdt.Edit.ready";';
      assert.equal(changed.split(anchor).length,2,control+' callee-prune anchor');
      changed=changed.replace(anchor,anchor+'\n    Tactics.prune "Nickel.EventGraph.readiness_is_exact";');
    }
    const view=original.slice(0,start)+changed+original.slice(end);await put(path.join(dir,name),view);
    const r=await verify({dir,roots:[path.join(dir,name)],fstar,models,modelCache});
    await fs.writeFile(path.join(output,control+'.proof.log'),r.log);
    assert(hasOrdinaryTheoremRejection({status:r.status,log:r.log,theorem:'Nickel.'+module+'.'+owner,view}),control+': '+r.log);
    console.log('PASS '+control+': ordinary owning rejection');
  }
}
