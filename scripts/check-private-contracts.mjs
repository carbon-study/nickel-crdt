// Tree publication -> plan -> receive: private-state contracts must carry callers.
import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import path from 'node:path';
import {put,verify} from './proof-cache.mjs';
import {hasOrdinaryTheoremRejection} from './negative-proof-evidence.mjs';
export async function checkPrivateContracts({proof,output,fstar,models,modelCache}) {
  const file=path.join(proof,'Nickel.EditCommit.fst'),original=await fs.readFile(file,'utf8');
  const treePattern=' [SMTPat (Native.impl_Replica__with_tree state tree)]';
  const planPattern=' [SMTPat (Native.impl_Replica__plan before fact)]';
  const treePrune='Tactics.prune "Nickel_crdt.Edit.impl_Replica__with_tree";';
  const planPrune='Tactics.prune "Nickel_crdt.Edit.impl_Replica__plan";';
  for(const needle of [treePattern,planPattern,treePrune,planPrune])assert.equal(original.split(needle).length,2);
  for(const [name,view,theorem]of[
    ['private-without-tree-pattern',original.replace(treePattern,''),'plan_preserves_private_state'],
    ['private-without-tree-contract',original.replace(treePrune,treePrune+'\n    Tactics.prune "Nickel.EditCommit.tree_publication_keeps_private";'),'plan_preserves_private_state'],
    ['private-without-plan-pattern',original.replace(planPattern,''),'receive_preserves_private_state'],
    ['private-without-plan-contract',original.replace(planPrune,planPrune+'\n    Tactics.prune "Nickel.EditCommit.plan_preserves_private_state";'),'receive_preserves_private_state'],
  ]) {
    try {
      await put(file,view);const result=await verify({dir:proof,roots:[file],fstar,models,modelCache});
      await fs.writeFile(path.join(output,name+'.proof.log'),result.log);
      assert(hasOrdinaryTheoremRejection({status:result.status,log:result.log,theorem:'Nickel.EditCommit.'+theorem,view}),
        'require ordinary private-state contract dependency rejection: '+result.log);
      console.log('PASS '+name+': actual private-state caller requires its contract');
    }finally{await put(file,original);}
  }
}
