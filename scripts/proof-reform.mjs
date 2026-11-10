// A source-style fence, not an isolation boundary or a proof about arbitrary aliases.
import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import path from 'node:path';
const forbidden=new Set(['norm','norm_spec','assert_norm','normalize_term','normalize','norm_term','reveal_opaque',
  'compute','delta','delta_only','delta_once','delta_namespace','unfold_def',
  'iota','zeta','zeta_full','primops','unmeta','unascribe']);
function tokens(source) {
  return [...source.matchAll(/\/\/[^\n]*|\/\*[\s\S]*?\*\/|"(?:\\.|[^"\\])*"|[A-Za-z_][A-Za-z0-9_']*|[^\s]/g)]
    .map(m=>m[0]).filter(t=>!t.startsWith('//')&&!t.startsWith('/*'));
}
const pastVisibility=new Set(['"Nickel_crdt.Edit.has_event"','"Nickel_crdt.Edit.extend_past"','"Nickel_crdt.Edit.past_pass"','"Nickel_crdt.Edit.past"']);
const pastTotalVisibility=new Set([...pastVisibility,'"Nickel_crdt.Edit.validate_after"','"Nickel_crdt.Edit.duplicate_events"']);
const causalVisibility=new Set([
  '"Nickel.EditCausal.causal_rank"',
  '"Nickel.EditIdentity.prefix_absent"','"Nickel_crdt.Edit.has_fact"','"Nickel_crdt.Edit.impl_Replica__new"','"Nickel_crdt.Edit.impl_Replica__receive"','"Nickel_crdt.Edit.impl_Replica__edit"']);
const atomicVisibility=new Set([
  '"Nickel_crdt.Edit.frontier"',
'"Alloc.Vec.impl__new"','"Nickel_crdt.Edit.impl_Replica__validate_new"','"Nickel_crdt.Edit.canonical"','"Nickel_crdt.Edit.interpret"']);
const wellFormedVisibility=new Set([
  '"Nickel_crdt.Edit.impl_Replica__new"',
  '"Nickel_crdt.Edit.validate_after"','"Nickel_crdt.Edit.past"','"Nickel_crdt.Edit.impl_Replica__validate_new"',
  '"Nickel_crdt.Edit.impl_Replica__receive"','"Nickel_crdt.Edit.impl_Replica__edit"',
  '"Nickel_crdt.Edit.validate_scalars"',
  '"Nickel.Vector.slice_index"','"Nickel.Vector.slice_length"','"Nickel_crdt.Edit.has_fact"',
  '"Nickel.EditIdentity.prefix_absent"'
]);
// Only the public Spec composition may hide these native operation facts.
const specVisibility=new Set([
  '"Nickel_crdt.Edit.impl_Replica__new"',
  '"Nickel_crdt.Edit.impl_Replica__receive"',
  '"Nickel_crdt.Edit.impl_Replica__edit"',
]);
const commitVisibility=new Set([
  '"Nickel_crdt.Edit.frontier"','"Nickel_crdt.Edit.impl_Replica__receive"','"Nickel_crdt.Edit.impl_Replica__edit"',
]);
// Accepted callers may hide these callee bodies, so their proofs go through the callee contracts.
const acceptedVisibility=new Set([
  '"Alloc.Vec.impl__new"','"Nickel_crdt.Edit.impl_Replica__new"',
  '"Nickel_crdt.Edit.canonical_step"','"Nickel_crdt.Edit.choose_unseen"','"Nickel_crdt.Edit.canonical"',
  '"Nickel_crdt.Edit.has_fact"','"Nickel_crdt.Edit.event_lt"','"Nickel_crdt.Edit.clone_selected_fact"','"Nickel_crdt.Edit.interpret"',
]);
export function assertReformedSource(name,source) {
  const ts=tokens(source),fail=message=>assert.fail(name+' reform: '+message);
  for(let i=0;i<ts.length;i++) {
    if(ts.slice(i,i+8).join(' ')==="import Tactics = FStar . Tactics . V2") { i+=7;continue; }
    if(forbidden.has(ts[i]))fail('explicit normalization is prohibited: '+ts[i]);
    if(ts[i]==='FStar'&&ts[i+1]==='.'&&ts[i+2]==='NormSteps')fail('normalizer imports are prohibited');
    if(ts[i]==='FStar'&&ts[i+1]==='.'&&ts[i+2]==='Tactics')
      fail('only the canonical Tactics import is approved');
    if(ts[i]==='Tactics'&&ts[i+1]==='.'&&ts[i+2]==='prune'&&ts[i+3]==='('&&ts[i+5]===')'&&
      ['"Nickel_crdt.Edit.impl_Replica__with_tree"','"Nickel_crdt.Edit.impl_Replica__plan"','"Nickel_crdt.Edit.impl_Replica__duplicate"','"Nickel_crdt.Edit.invalid"','"Nickel_crdt.Edit.writer_index"','"Nickel_crdt.Edit.fact_equal"','"Alloc.Vec.from_seq"','"Alloc.Vec.impl_1__as_slice"','"Alloc.Vec.impl_1__len"','"Core_models.Slice.impl__len"','"Rust_primitives.Slice.slice_index"','"Nickel_crdt.Edit.push"','"Nickel_crdt.Edit.impl_Replica__with_counter"','"Nickel_crdt.Edit.next_counter_after"','"Rust_primitives.Hax.Folds.fold_range"','"Rust_primitives.Hax.Folds.fold_range_return"','"Nickel.LoopUtil.option_run"','"Nickel.LoopUtil.step_safe"','"Nickel.LoopUtil.output_safe"','"Nickel_proof_smoke.flip"'].includes(ts[i+4])) { i+=5;continue; }
    if(name==='LoopUtil'&&ts[i]==='Tactics'&&ts[i+1]==='.'&&ts[i+2]==='prune'&&ts[i+3]==='('&&ts[i+4]==='"Rust_primitives.Hax.Folds.fold_range_cf"'&&ts[i+5]===')') { i+=5;continue; }
    if(name==='EditWellFormed'&&ts[i]==='Tactics'&&ts[i+1]==='.'&&ts[i+2]==='prune'&&ts[i+3]==='('&&ts[i+5]===')'&&wellFormedVisibility.has(ts[i+4])) { i+=5;continue; }
    if(name==='Spec'&&ts[i]==='Tactics'&&ts[i+1]==='.'&&ts[i+2]==='prune'&&ts[i+3]==='('&&ts[i+5]===')'&&specVisibility.has(ts[i+4])) { i+=5;continue; }
    if(name==='EditAccepted'&&ts[i]==='Tactics'&&ts[i+1]==='.'&&ts[i+2]==='prune'&&ts[i+3]==='('&&ts[i+5]===')'&&acceptedVisibility.has(ts[i+4])) { i+=5;continue; }
    if(name==='EditCommit'&&ts[i]==='Tactics'&&ts[i+1]==='.'&&ts[i+2]==='prune'&&ts[i+3]==='('&&ts[i+5]===')'&&commitVisibility.has(ts[i+4])) { i+=5;continue; }
    if(name==='EditAtomic'&&ts[i]==='Tactics'&&ts[i+1]==='.'&&ts[i+2]==='prune'&&ts[i+3]==='('&&ts[i+5]===')'&&atomicVisibility.has(ts[i+4])) { i+=5;continue; }
    if(name==='EditSchedule'&&ts[i]==='Tactics'&&ts[i+1]==='.'&&ts[i+2]==='prune'&&ts[i+3]==='('&&ts[i+5]===')'&&['"Nickel_crdt.Edit.has_event"','"Nickel_crdt.Edit.ready"','"Nickel_crdt.Edit.choose_ready"'].includes(ts[i+4])) { i+=5;continue; }
    if(name==='EditPast'&&ts[i]==='Tactics'&&ts[i+1]==='.'&&ts[i+2]==='prune'&&ts[i+3]==='('&&ts[i+5]===')'&&pastVisibility.has(ts[i+4])) { i+=5;continue; }
    if(name==='EditPastTotal'&&ts[i]==='Tactics'&&ts[i+1]==='.'&&ts[i+2]==='prune'&&ts[i+3]==='('&&ts[i+5]===')'&&pastTotalVisibility.has(ts[i+4])) { i+=5;continue; }
    if(name==='EditCausal'&&ts[i]==='Tactics'&&ts[i+1]==='.'&&ts[i+2]==='prune'&&ts[i+3]==='('&&ts[i+5]===')'&&causalVisibility.has(ts[i+4])) { i+=5;continue; }
    if(ts[i]==='Tactics') {
      // No aliasing even of approved methods: only this direct call is admitted.
      if(ts.slice(i,i+8).join(' ')!=="Tactics . smt_sync' ( 1 , 1 )")
        fail('only approved direct SMT/visibility tactic calls are permitted');
      i+=7;
    }
  }
}
export async function checkProofReform(root,names=['EditAtomic','LoopUtil','Smoke','Vector','EditCausal','EditIdentity','EditWellFormed','Spec','EditCommit','EditAccepted','EditPast','EditPastTotal','EditSchedule']) {
  for(const name of names)assertReformedSource(name,await fs.readFile(path.join(root,'proofs',name+'.lt'),'utf8'));
}
