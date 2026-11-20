// Complete helper-produced operation replay and its public erasure boundary.
import assert from 'node:assert/strict';
import {viewUnits} from './text-family-run.mjs';
export function operationUnits(read) {
  const name='Nickel.EditSchedule.fst', original=read(name);
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

  const units=[];
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
    const view=original.slice(0,start)+body.replace(pattern,replacement)+original.slice(end);
    units.push({name:control,files:{[name]:view},roots:[name],theorem:'Nickel.EditSchedule.'+owner,inPlace:false,
      log:control+'.proof.log',pass:control+': ordinary owning rejection',failure:control});
  }
  return viewUnits('operation',units,read);
}
