// Ordered selected-group replay, error propagation and actual context composition.
import assert from 'node:assert/strict';
import {viewUnits} from './text-family-run.mjs';
export function replayUnits(read) {
  const name='Nickel.EditReplay.fst', original=read(name);
  const controls=[
    ['replay-result-without-induction',/author_prefix_is_deterministic operations selected \(finish - 1\) previous_left previous_right;/,'author_prefix_is_deterministic','author_prefix_is_deterministic','();'],
    ['replay-nodes-without-loop',/  Nickel\.LoopUtil\.result_preserve_any [^\n]+;\n/,'actual_nodes_replay_in_order','actual_nodes_replay_in_order'],
    ['replay-nodes-without-terminal',/node_error_is_terminal nodes initial \(v index \+ 1\) \(Seq\.length nodes\) error/,'actual_nodes_replay_in_order','actual_nodes_replay_in_order','()'],
    ['replay-author-without-loop',/  Nickel\.LoopUtil\.result_preserve_any [^\n]+;\n/,'actual_author_replays_selected_groups','actual_author_replays_selected_groups'],
    ['replay-author-without-nodes',/actual_nodes_replay_in_order \(Alloc\.Vec\.impl_1__as_slice nodes\) tree/,'actual_author_replays_selected_groups','actual_author_replays_selected_groups','()'],
    ['replay-author-without-terminal',/author_error_is_terminal operations selected \(v index \+ 1\) \(Seq\.length operations\) error/,'actual_author_replays_selected_groups','actual_author_replays_selected_groups','()'],
    ['replay-context-without-basis',/  closed_event_basis_is_exact facts event;\n/,'closed_author_context_is_exact','closed_author_context_is_exact'],
    ['replay-context-without-author',/actual_author_replays_selected_groups operations \(Alloc\.Vec\.impl_1__as_slice selected\)/,'closed_author_context_is_exact','closed_author_context_is_exact','()'],
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
    units.push({name:control,files:{[name]:view},roots:[name],theorem:'Nickel.EditReplay.'+owner,inPlace:false,
      log:control+'.proof.log',pass:control+': ordinary owning rejection',failure:control});
  }
  return viewUnits('replay',units,read);
}
