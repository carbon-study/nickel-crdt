// Accepted callers withhold their callee bodies; each must then fail at its owner
// when the contract it composes is withheld too.
import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import path from 'node:path';
import {put,verify} from './proof-cache.mjs';
import {hasOrdinaryTheoremRejection} from './negative-proof-evidence.mjs';
export async function checkAcceptedContracts({proof,output,fstar,models,modelCache}) {
  const file=path.join(proof,'Nickel.EditAccepted.fst'),original=await fs.readFile(file,'utf8');
  function declaration(theorem) {
    const start=original.indexOf('let '+theorem+' ');assert(start>=0,theorem);
    const next=/\n(?:let (?:rec )?\w+ |open |type |module |val )/.exec(original.slice(start+4));
    const end=next?start+4+next.index:original.length;
    return {start,end,body:original.slice(start,end)};
  }
  // Replace one needle inside one named declaration only.
  function withhold(theorem,needle,replacement) {
    const {start,end,body}=declaration(theorem);
    assert.equal(body.split(needle).length,2,theorem+': '+needle);
    return original.slice(0,start)+body.replace(needle,replacement)+original.slice(end);
  }
  const step=' [SMTPat (Native.canonical_step input out)]',tree=' [SMTPat (Native.impl_Replica__with_tree state tree)]';
  const cases=[
    ['accepted-least-without-step','selected_id_is_least','least_extends_all input out;','();'],
    ['accepted-order-without-step-contract','canonical_orders_facts',step,''],
    ['accepted-progress-without-step-contract','canonical_succeeds_for_unique_ids',step,''],
    ['accepted-step-without-push-contract','canonical_step_succeeds','push_result_is_exact out (Native.clone_selected_fact (Rust_primitives.Slice.slice_index input k));','();'],
    ['accepted-frontier-without-bound','append_least_preserves_frontier','frontier_bounds_unseen input out i j;','();'],
    ['accepted-frontier-without-membership','append_least_preserves_frontier','push_membership out fact (Rust_primitives.Slice.slice_index input j).f_id;','();'],
    ['accepted-publication-without-tree-contract','plan_publishes_canonical_facts',tree,''],
    // Result-shape patterns restore only the withheld callees' declared result types.
    ['accepted-publication-without-canonical-shape','canonical_has_result_shape',' [SMTPat (Native.canonical input)]','','plan_publishes_canonical_facts'],
    ['accepted-publication-without-interpret-shape','interpret_has_result_shape',' [SMTPat (Native.interpret input)]','','plan_publishes_canonical_facts'],
    ['accepted-interpretation-without-tree-contract','plan_publishes_interpretation','f_tree == tree)'+tree,'f_tree == tree)'],
  ];
  for(const owner of ['selected_id_is_unseen','canonical_has_unique_ids','canonical_selects_whole_facts','selected_id_is_least','canonical_orders_facts','choice_always_returns','canonical_succeeds_for_unique_ids']) {
    const {body}=declaration(owner);
    const calls=[...body.matchAll(/^  Nickel\.LoopUtil\.result_preserve_any [^\n]+;$/gm)];
    assert.equal(calls.length,1,owner+': one Result-rule call');
    cases.push(['accepted-loop-without-result-rule-'+owner,owner,calls[0][0],'  ();']);
  }
  for(const owner of ['canonical_has_unique_ids','canonical_selects_whole_facts','canonical_orders_facts','canonical_succeeds_for_unique_ids']) {
    const {body}=declaration(owner);
    const calls=[...body.matchAll(/^  canonical_uses_complete_range [^\n]+;$/gm)];
    assert.equal(calls.length,1,owner+': one source-frame call');
    cases.push(['accepted-loop-without-source-frame-'+owner,owner,calls[0][0],'  ();']);
  }
  for(const[name,scope,needle,replacement,owner=scope]of cases) {
    const view=withhold(scope,needle,replacement),theorem=owner;
    try {await put(file,view);const result=await verify({dir:proof,roots:[file],fstar,models,modelCache});
      await fs.writeFile(path.join(output,name+'.proof.log'),result.log);
      assert(hasOrdinaryTheoremRejection({status:result.status,log:result.log,theorem:'Nickel.EditAccepted.'+theorem,view}),'require ordinary accepted dependency rejection: '+result.log);
      console.log('PASS '+name+': caller needs its checked contract');
    }finally{await put(file,original);}
  }
}
