// Empirical visibility family: NOT a consequence of the origin-relative
// insertion-only simulation. A hidden node can interrupt a whole-order run.
import assert from 'node:assert/strict';
import {author,eventId} from './order.mjs';
import {fugueInterpret,fugueIds,causalSchedules} from './fugue.mjs';
export function hiddenInsideRuns() {
  const receipt={histories:0,causalSchedules:0,wholeOrderSplitHistories:0,examples:[],
    scope:'supplied visibility; no real Undo/Restore transitions or general visible-run theorem'};
  for(const swap of [false,true])for(let mask=0;mask<4;mask++) {
    const root=author([],0,1,'ab',[],0),base=fugueIds([root]);
    const alice=swap?3:1,carol=swap?1:3;
    const one=author([root],alice,1,'1',base,1);
    const three=author([root],carol,1,'3',base,1);
    const left=[root,one],right=[root,three],hidden=new Set();
    if(mask&1) {
      const h=author(left,2,1,'h',fugueIds(left),1);left.push(h);hidden.add(`${eventId(h)}/0`);
    }
    const two=author(left,alice,2,'2',fugueIds(left).filter(id=>!hidden.has(id)),1);left.push(two);
    if(mask&2) {
      const k=author(right,carol,2,'k',fugueIds(right),1);right.push(k);hidden.add(`${eventId(k)}/0`);
    }
    const four=author(right,carol,mask&2?3:2,'4',fugueIds(right).filter(id=>!hidden.has(id)),1);right.push(four);
    const history=[root,...left.slice(1),...right.slice(1)],canonical=fugueInterpret(history);
    const text=rows=>rows.map(e=>e.scalar).join('');
    const expected=swap?'a4321b':'a2143b';
    assert.equal(text(canonical.filter(e=>!hidden.has(e.id))),expected,'visible empirical prepend run');
    if(hidden.size) {
      assert.notEqual(text(canonical),expected,'whole order must retain hidden interruption');
      receipt.wholeOrderSplitHistories++;
    }
    for(const schedule of causalSchedules(history)) {
      const rows=fugueInterpret(schedule);assert.deepEqual(rows,canonical,'hidden-run delivery agreement');
      assert.equal(text(rows.filter(e=>!hidden.has(e.id))),expected,'hidden-run visible contiguity');
      receipt.causalSchedules++;
    }
    assert.deepEqual(fugueInterpret(JSON.parse(JSON.stringify(history)).reverse()),canonical,'hidden-run cold reconstruction');
    if(mask===3)receipt.examples.push({whole:text(canonical),visible:expected});
    receipt.histories++;
  }
  return receipt;
}
