// The source-bound commit laws compose the exact receive and counter contracts.
import assert from 'node:assert/strict';
import {viewUnits} from './text-family-run.mjs';
export function commitUnits(read) {
  const file='Nickel.EditCommit.fst',original=read(file);
  function change(name,needle,replacement) {
    const start=original.indexOf('let '+name+' ');assert(start>=0);
    const next=/\nlet (?:rec )?\w+ /.exec(original.slice(start+4)),end=next?start+4+next.index:original.length;
    const body=original.slice(start,end);assert.equal(body.split(needle).length,2);
    return original.slice(0,start)+body.replace(needle,replacement)+original.slice(end);
  }
  const same='authored_fact_replays_same_commit',derived='local_author_remote_admit',privateName='receive_preserves_private_state',shared='admission_ignores_private_state';
  const cases=[
    ['commit-without-receive',same,'receive_uses_plan before fact;','() ;'],
    ['commit-without-counter',same,'Nickel.EditAtomic.counter_result_is_exact before.f_next_counter;','() ;'],
    ['commit-without-setter',same,'Tactics.prune "Nickel_crdt.Edit.impl_Replica__with_counter";','Tactics.prune "Nickel_crdt.Edit.impl_Replica__with_counter";\n    Tactics.prune "Nickel.EditAtomic.counter_installation_is_exact";'],
    ['private-without-receive',privateName,'receive_uses_plan before fact;','() ;'],
    ['shared-without-before-receive',shared,'receive_uses_plan before fact;','() ;'],
    ['shared-without-remote-receive',shared,'receive_uses_plan remote fact;','() ;'],
    ['delivery-without-commit',derived,'authored_fact_replays_same_commit before gap insert delete;','() ;'],
    ['delivery-without-admission',derived,'admission_ignores_private_state before remote fact;','() ;'],
    ['delivery-without-private',derived,'receive_preserves_private_state remote fact;','() ;'],
  ];
  return viewUnits('commit',cases.map(([name,theorem,needle,replacement])=>({name,files:{[file]:change(theorem,needle,replacement)},roots:[file],theorem:'Nickel.EditCommit.'+theorem,inPlace:true,
    log:name+'.proof.log',pass:name+': caller needs its checked contract',failure:'require ordinary commit contract rejection'})),read);
}
