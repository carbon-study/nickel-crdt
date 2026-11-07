// The same-history admission law must compose checked relational callees.
import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import path from 'node:path';
import {put,verify} from './proof-cache.mjs';
import {hasOrdinaryTheoremRejection} from './negative-proof-evidence.mjs';
export async function checkSharedContracts({proof,output,fstar,models,modelCache}) {
  const file=path.join(proof,'Nickel.EditCommit.fst'),original=await fs.readFile(file,'utf8');
  const treePattern=' [SMTPat (Native.impl_Replica__with_tree left tree); SMTPat (Native.impl_Replica__with_tree right tree)]';
  const planPattern=' [SMTPat (Native.impl_Replica__plan before fact); SMTPat (Native.impl_Replica__plan remote fact)]';
  for(const p of [treePattern,planPattern])assert.equal(original.split(p).length,2);
  function withholdAt(name,needle,law) {
    const start=original.indexOf('let '+name+' ');assert(start>=0);
    const next=/\nlet (?:rec )?\w+ /.exec(original.slice(start+4));
    const end=next?start+4+next.index:original.length,body=original.slice(start,end);
    assert.equal(body.split(needle).length,2);
    return original.slice(0,start)+body.replace(needle,needle+'\n    Tactics.prune "'+law+'";')+original.slice(end);
  }
  for(const [name,view,theorem]of[
    ['shared-without-tree-pattern',original.replace(treePattern,''),'plan_ignores_private_state'],
    ['shared-without-tree-contract',withholdAt('plan_ignores_private_state','Tactics.prune "Nickel_crdt.Edit.impl_Replica__with_tree";','Nickel.EditCommit.tree_publication_respects_shared'),'plan_ignores_private_state'],
    ['shared-without-plan-pattern',original.replace(planPattern,''),'admission_ignores_private_state'],
    ['shared-without-plan-contract',withholdAt('admission_ignores_private_state','Tactics.prune "Nickel_crdt.Edit.impl_Replica__plan";','Nickel.EditCommit.plan_ignores_private_state'),'admission_ignores_private_state'],
  ]) {
    try {
      await put(file,view);const result=await verify({dir:proof,roots:[file],fstar,models,modelCache});
      await fs.writeFile(path.join(output,name+'.proof.log'),result.log);
      assert(hasOrdinaryTheoremRejection({status:result.status,log:result.log,theorem:'Nickel.EditCommit.'+theorem,view}),
        'require ordinary shared-state contract dependency rejection: '+result.log);
      console.log('PASS '+name+': actual same-history caller requires its contract');
    }finally{await put(file,original);}
  }
}
