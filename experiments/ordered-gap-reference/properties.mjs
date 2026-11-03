import assert from 'node:assert/strict';
import {interpret,eventId,elementId} from './order.mjs';
// An author-snapshot property. Unknown concurrent nodes are deliberately absent.
export function wholeGap(events,event,options={}) {
  const before=interpret(events,options),seen=new Set(event.visible);
  const view=before.filter(r=>seen.has(r.id));
  const left=event.gap?view[event.gap-1]:null;
  const after=interpret([...events,event],options);
  const at=left?after.findIndex(r=>r.id===left.id)+1:0;
  const expected=[...event.text].map((_,i)=>elementId(event,i));
  assert.deepEqual(after.slice(at,at+expected.length).map(r=>r.id),expected,
    'new insertion must immediately follow its visible predecessor in the whole known order');
}
export function eventCohesion(events,records=interpret(events)) {
  const at=new Map(records.map((r,i)=>[r.id,i]));
  for(let i=0;i<events.length;i++)for(let j=i+1;j<events.length;j++) {
    const a=events[i],b=events[j];
    if(a.basis.includes(eventId(b))||b.basis.includes(eventId(a)))continue;
    const indices=e=>[...e.text].map((_,k)=>at.get(elementId(e,k)));
    const x=indices(a),y=indices(b);
    assert(Math.max(...x)<Math.min(...y)||Math.max(...y)<Math.min(...x),
      'mutually concurrent insertion events must not interleave');
  }
}
