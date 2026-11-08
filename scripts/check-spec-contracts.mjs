// Each headline composes explicit public contracts with native operations hidden.
// Patternless lemmas supply local posts through calls, not automatic global facts.
import fs from 'node:fs/promises';
import path from 'node:path';
import assert from 'node:assert/strict';
import {put,verify} from './proof-cache.mjs';
import {hasOrdinaryTheoremRejection} from './negative-proof-evidence.mjs';
export async function checkSpecContracts({proof,output,fstar,models,modelCache}) {
  const file=path.join(proof,'Nickel.Spec.fst'),original=await fs.readFile(file,'utf8');
  const cases=[
    ['new_establishes_valid_facts', ['Accepted.new_establishes_unique_ids','Accepted.new_establishes_fact_order','WellFormed.new_establishes_scalar_validity','WellFormed.new_establishes_causal_closure']],
    ['receive_preserves_valid_facts',['Accepted.receive_preserves_unique_ids','Accepted.receive_preserves_fact_order','WellFormed.receive_preserves_scalar_validity','WellFormed.receive_preserves_causal_closure']],
    ['edit_preserves_valid_facts',['Accepted.edit_preserves_unique_ids','Accepted.edit_preserves_fact_order','WellFormed.edit_preserves_scalar_validity','WellFormed.edit_preserves_causal_closure']],
    ['receive_obeys_contract',[
      'Atomic.receive_rejection_unchanged','Commit.receive_preserves_private_state',
      'Accepted.receive_added_has_exact_contents','Identity.receive_added_has_fresh_event_id',
      'Accepted.receive_added_ids_are_unique','Accepted.receive_added_facts_are_ordered',
      'WellFormed.receive_added_fact_has_valid_scalars','WellFormed.receive_added_has_direct_dependencies']],
    ['edit_obeys_contract',[
      'Atomic.edit_rejection_or_empty_unchanged','Atomic.authored_edit_advances_once',
      'Commit.authored_fact_binds_request','Commit.authored_fact_replays_same_commit',
      'Accepted.edit_authored_has_exact_contents','Identity.authored_event_id_is_fresh',
      'Accepted.authored_facts_are_ordered','WellFormed.edit_authors_only_valid_scalars']],
    ['known_identity_is_classified',['Identity.receive_known_identity']],
    ['invalid_counter_is_rejected',['Identity.receive_invalid_counter']],
    ['equal_shared_history_gives_same_admission',['Commit.admission_ignores_private_state']],
    ['authored_fact_admits_on_equal_shared_history',['Commit.local_author_remote_admit']],
    ['equal_candidate_contents_give_same_rebuild',['Accepted.receive_added_shared_state_agrees']],
  ];
  for(const [headline,contracts] of cases) for(const contract of contracts) {
    const start=original.indexOf('let '+headline+' ');assert(start>=0,'missing headline '+headline);
    const tail=original.slice(start+4),next=/\nlet (?:rec )?\w+ /.exec(tail),end=next?start+4+next.index:original.length;
    const body=original.slice(start,end);
    const needle=body.split('\n').find(line=>line.startsWith('  '+contract+' '));assert(needle,'missing explicit contract call '+contract);
    assert.equal(body.split(needle).length,2);
    const mutant=original.slice(0,start)+body.replace(needle,'  ();')+original.slice(end),theorem='Nickel.Spec.'+headline;
    const name='spec-without-'+contract.split('.').at(-1);
    try {
      await put(file,mutant);
      const result=await verify({dir:proof,roots:[file],fstar,models,modelCache});
      await fs.writeFile(path.join(output,name+'.proof.log'),result.log);
      assert(hasOrdinaryTheoremRejection({status:result.status,log:result.log,theorem,view:mutant}),'expected ordinary headline rejection without '+contract+': '+result.log);
      console.log('PASS '+name+': headline needs the explicit checked contract');
    } finally { await put(file,original); }
  }
}
