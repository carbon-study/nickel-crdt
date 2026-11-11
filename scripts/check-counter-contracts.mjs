// Proof-dependency controls, distinct from actual-Rust semantic mutants.
import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import path from 'node:path';
import {put,verify} from './proof-cache.mjs';
import {hasOrdinaryTheoremRejection} from './negative-proof-evidence.mjs';
export async function checkCounterContracts({proof,output,fstar,models,modelCache}) {
  const original=await fs.readFile(path.join(proof,'Nickel.EditAtomic.fst'),'utf8');
  const controls=[
    ['counter-without-setter-pattern',' [SMTPat (Native.impl_Replica__with_counter state counter)]'],
    ['counter-without-calculator-contract','  counter_result_is_exact before.f_next_counter;\n'],
  ];
  for(const [name,needle] of controls) {
    assert.equal(original.split(needle).length,2,'contract-control anchor must occur exactly once');
    const dir=path.join(path.dirname(proof),name);
    await fs.rm(dir,{recursive:true,force:true});
    await fs.cp(proof,dir,{recursive:true,preserveTimestamps:true});
    const view=original.replace(needle,'');await put(path.join(dir,'Nickel.EditAtomic.fst'),view);
    const result=await verify({dir,roots:[path.join(dir,'Nickel.EditAtomic.fst')],fstar,models,modelCache});
    await fs.writeFile(path.join(output,name+'.proof.log'),result.log);
    assert(hasOrdinaryTheoremRejection({status:result.status,log:result.log,
      theorem:'Nickel.EditAtomic.authored_edit_advances_once',view}),
      'require ordinary public-counter rejection after removing its contract dependency: '+result.log);
    console.log('PASS '+name+': unchanged public theorem requires its callee contract');
  }
}
