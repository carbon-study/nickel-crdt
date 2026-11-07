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
export function assertReformedSource(name,source) {
  const ts=tokens(source),fail=message=>assert.fail(name+' reform: '+message);
  for(let i=0;i<ts.length;i++) {
    if(ts.slice(i,i+8).join(' ')==="import Tactics = FStar . Tactics . V2") { i+=7;continue; }
    if(forbidden.has(ts[i]))fail('explicit normalization is prohibited: '+ts[i]);
    if(ts[i]==='FStar'&&ts[i+1]==='.'&&ts[i+2]==='NormSteps')fail('normalizer imports are prohibited');
    if(ts[i]==='FStar'&&ts[i+1]==='.'&&ts[i+2]==='Tactics')
      fail('only the canonical Tactics import is approved');
    if(ts[i]==='Tactics'&&ts[i+1]==='.'&&ts[i+2]==='prune'&&ts[i+3]==='('&&ts[i+5]===')'&&
      ['"Nickel_crdt.Edit.impl_Replica__plan"','"Nickel_crdt.Edit.impl_Replica__duplicate"','"Nickel_crdt.Edit.invalid"','"Nickel_crdt.Edit.writer_index"','"Nickel_crdt.Edit.fact_equal"','"Alloc.Vec.from_seq"','"Alloc.Vec.impl_1__as_slice"','"Alloc.Vec.impl_1__len"','"Core_models.Slice.impl__len"','"Rust_primitives.Slice.slice_index"','"Nickel_crdt.Edit.push"','"Nickel_crdt.Edit.impl_Replica__with_counter"','"Nickel_crdt.Edit.next_counter_after"','"Rust_primitives.Hax.Folds.fold_range"','"Rust_primitives.Hax.Folds.fold_range_return"','"Nickel.LoopUtil.option_run"','"Nickel.LoopUtil.step_safe"','"Nickel.LoopUtil.output_safe"','"Nickel_proof_smoke.flip"'].includes(ts[i+4])) { i+=5;continue; }
    if(ts[i]==='Tactics') {
      // No aliasing even of approved methods: only this direct call is admitted.
      if(ts.slice(i,i+8).join(' ')!=="Tactics . smt_sync' ( 1 , 1 )")
        fail('only approved direct SMT/visibility tactic calls are permitted');
      i+=7;
    }
  }
}
export async function checkProofReform(root,names=['EditAtomic','LoopUtil','Smoke','Vector','EditIdentity']) {
  for(const name of names)assertReformedSource(name,await fs.readFile(path.join(root,'proofs',name+'.lt'),'utf8'));
  // These scalar boundaries and the declarations below have migrated; other WellFormed proofs remain open.
  const source=await fs.readFile(path.join(root,'proofs','EditWellFormed.lt'),'utf8');
  const start=source.indexOf('proof scalar_validation_is_sound('),end=source.indexOf('function fact_scalars_valid(',start);
  assert(start>=0&&end>start,'scalar reform scope must remain present');
  assertReformedSource('EditWellFormed.scalar-boundaries',source.slice(start,end));
  // Declarations whose redundant reductions were deleted and that contain no other normalization.
  // The two containment lemmas keep their reductions; two scalar proofs still use Tactics.norm.
  for(const name of ['receive_preserves_scalar_validity','edit_authors_only_valid_scalars','edit_preserves_scalar_validity','new_establishes_scalar_validity','event_membership_is_presence','dependency_validation_is_sound','present_dependencies_pass_guard','successful_past_has_direct_dependencies','dependencies_survive_containment','exact_extension_preserves_causal_closure','receive_preserves_causal_closure','edit_preserves_causal_closure','new_establishes_causal_closure']) {
    const match=new RegExp('^proof!? '+name+'[<(]','m').exec(source);assert(match,'missing reformed WellFormed declaration '+name);
    const tail=source.slice(match.index+match[0].length),next=/\n(?:function|proof!?|type|import) /.exec(tail);
    assertReformedSource('EditWellFormed.'+name,source.slice(match.index,next?match.index+match[0].length+next.index:source.length));
  }
  const accepted=await fs.readFile(path.join(root,'proofs','EditAccepted.lt'),'utf8');
  for(const name of ['push_outcome','push_result_is_exact','append_fresh_preserves_unique','append_whole_fact','push_has_exact_contents','push_membership','member_lookup','absent_lookup','event_order_is_key_order']) {
    const match=new RegExp('^(?:function!?|proof!?) '+name+'[<(]','m').exec(accepted);assert(match,'missing reformed Accepted declaration '+name);
    const tail=accepted.slice(match.index+match[0].length),next=/\n(?:function|proof!?|type|import) /.exec(tail);
    const end=next?match.index+match[0].length+next.index:accepted.length;
    assertReformedSource('EditAccepted.'+name,accepted.slice(match.index,end));
  }
}
