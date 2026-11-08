// Each headline composes four proved public contracts. Its native operation
// and the global facts of those contracts are withheld in the caller query.
import fs from 'node:fs/promises';
import path from 'node:path';
import assert from 'node:assert/strict';
import {put,verify} from './proof-cache.mjs';
import {hasOrdinaryTheoremRejection} from './negative-proof-evidence.mjs';
export async function checkSpecContracts({proof,output,fstar,models,modelCache}) {
  const file=path.join(proof,'Nickel.Spec.fst'),original=await fs.readFile(file,'utf8');
  for(const [operation,suffix,contracts] of [
    ['new','establishes', ['Accepted.new_establishes_unique_ids','Accepted.new_establishes_fact_order','WellFormed.new_establishes_scalar_validity','WellFormed.new_establishes_causal_closure']],
    ['receive','preserves',['Accepted.receive_preserves_unique_ids','Accepted.receive_preserves_fact_order','WellFormed.receive_preserves_scalar_validity','WellFormed.receive_preserves_causal_closure']],
    ['edit','preserves',['Accepted.edit_preserves_unique_ids','Accepted.edit_preserves_fact_order','WellFormed.edit_preserves_scalar_validity','WellFormed.edit_preserves_causal_closure']],
  ]) for(const contract of contracts) {
    const needle=original.split('\n').find(line=>line.startsWith('  '+contract+' '));assert(needle,'missing explicit contract call '+contract);
    assert.equal(original.split(needle).length,2);
    const mutant=original.replace(needle,'  ();'),theorem='Nickel.Spec.'+operation+'_'+suffix+'_valid_facts';
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
