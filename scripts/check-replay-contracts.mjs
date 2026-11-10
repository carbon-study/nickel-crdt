// Ordered selected-group replay, error propagation and actual context composition.
import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import path from 'node:path';
import {put,verify} from './proof-cache.mjs';
import {hasOrdinaryTheoremRejection} from './negative-proof-evidence.mjs';
export async function checkReplayContracts({proof,output,fstar,models,modelCache}) {
  const name='Nickel.EditReplay.fst', original=await fs.readFile(path.join(proof,name),'utf8');
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
    assert(hasOrdinaryTheoremRejection({status:r.status,log:r.log,theorem:'Nickel.EditReplay.'+owner,view}),control+': '+r.log);
    console.log('PASS '+control+': ordinary owning rejection');
  }
}
