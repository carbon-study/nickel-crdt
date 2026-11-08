// Separate constructor information from the planner's duplicate/error prefix.
import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import path from 'node:path';
import {put,verify} from './proof-cache.mjs';
import {hasOrdinaryTheoremRejection} from './negative-proof-evidence.mjs';
export async function checkPlanContracts({proof,output,fstar,models,modelCache}) {
  const atomicFile=path.join(proof,'Nickel.EditAtomic.fst');
  const identityFile=path.join(proof,'Nickel.EditIdentity.fst');
  const atomic=await fs.readFile(atomicFile,'utf8');
  const identity=await fs.readFile(identityFile,'utf8');
  const needle='Tactics.prune "Nickel_crdt.Edit.impl_Replica__plan";';
  const pattern=' [SMTPat (Native.impl_Replica__plan before fact)]';
  assert.equal(atomic.split(pattern).length,3);
  function withholdShapeAtCaller() {
    const start=atomic.indexOf('let authored_edit_advances_once ');assert(start>=0);
    const next=/\nlet (?:rec )?\w+ /.exec(atomic.slice(start+4));
    const end=next?start+4+next.index:atomic.length;
    const body=atomic.slice(start,end);assert.equal(body.split(needle).length,2);
    return atomic.slice(0,start)+body.replace(needle,
      needle+'\n    Tactics.prune "Nickel.EditAtomic.plan_has_result_shape";')+atomic.slice(end);
  }
  function withoutPattern(name) {
    const start=atomic.indexOf('let '+name+' ');assert(start>=0);
    const at=atomic.indexOf(pattern,start);assert(at>start);
    assert(!atomic.slice(start,at).includes('\nlet '));
    return atomic.slice(0,at)+atomic.slice(at+pattern.length);
  }
  const cases=[
    ['plan-without-shape-pattern',atomicFile,withoutPattern('plan_has_result_shape'),atomicFile,'Nickel.EditAtomic.authored_edit_advances_once'],
    ['plan-without-shape-contract',atomicFile,withholdShapeAtCaller(),atomicFile,'Nickel.EditAtomic.authored_edit_advances_once'],
    ['plan-without-prefix-pattern',atomicFile,withoutPattern('plan_preserves_duplicate_result'),identityFile,'Nickel.EditIdentity.receive_known_identity'],
  ];
  for(const name of ['receive_known_identity','receive_invalid_counter','receive_added_has_fresh_event_id']) {
    const start=identity.indexOf('let '+name+' ');assert(start>=0);
    const next=/\nlet (?:rec )?\w+ /.exec(identity.slice(start+4));
    const end=next?start+4+next.index:identity.length;
    const body=identity.slice(start,end);assert.equal(body.split(needle).length,2);
    const view=identity.slice(0,start)+body.replace(needle,needle+'\n    Tactics.prune "Nickel.EditAtomic.plan_preserves_duplicate_result";')+identity.slice(end);
    cases.push(['plan-without-prefix-'+name,identityFile,view,identityFile,'Nickel.EditIdentity.'+name]);
  }
  for(const [name,file,view,root,theorem]of cases) {
    try {
      await put(file,view);
      const result=await verify({dir:proof,roots:[root],fstar,models,modelCache});
      await fs.writeFile(path.join(output,name+'.proof.log'),result.log);
      const owner=file===root?view:identity;
      assert(hasOrdinaryTheoremRejection({status:result.status,log:result.log,theorem,view:owner}),
        'require ordinary plan-contract dependency rejection: '+result.log);
      console.log('PASS '+name+': actual caller requires the selected plan contract');
    }finally{await put(atomicFile,atomic);await put(identityFile,identity);}
  }
}
