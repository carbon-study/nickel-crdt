// Authored research reference, not Nickel's adopted order or undo engine.
import assert from 'node:assert/strict';
export const compare = (a,b) => {
  for(let i=0;i<Math.min(a.length,b.length);i++) {
    for(let j=0;j<4;j++) { if(a[i][j]!==b[i][j]) return a[i][j]<b[i][j]?-1:1; }
  }
  return Math.sign(a.length-b.length);
};
export const elementId=(event,index)=>`${event.writer}:${event.counter}/${index}`;
export const eventId=event=>`${event.writer}:${event.counter}`;
const clone=x=>JSON.parse(JSON.stringify(x));
const sorted=records=>[...records].sort((a,b)=>compare(a.key,b.key));
function between(left,right,tag) {
  // bottom = []; top = null. Every actual key is nonempty.
  assert(right===null || compare(left,right)<0,'nonempty interval');
  let h=0;
  if(right && left.length<right.length && left.every((d,i)=>d.every((x,j)=>x===right[i][j]))) h=right[left.length][0]-1;
  assert(Number.isSafeInteger(h),'reference integer bound');
  const key=[...clone(left),[h,...tag]];
  assert(compare(left,key)<0 && (right===null || compare(key,right)<0));
  return key;
}
export function author(events,writer,counter,text,visible,gap) {
  const basis=events.map(eventId).sort();
  return {writer,counter,text,basis,visible:[...visible].sort(),gap};
}
export function interpret(events,{receiverBasis=false,visibleRight=false}={}) {
  const records=[],done=new Map(),pending=clone(events);
  while(pending.length) {
    const at=pending.findIndex(e=>e.basis.every(id=>done.has(id)));
    assert(at>=0,'missing dependency or cycle');
    const [e]=pending.splice(at,1),id=eventId(e);
    if(done.has(id)) {assert.deepEqual(done.get(id),e,'conflicting duplicate');continue;}
    assert(Number.isSafeInteger(e.writer)&&e.writer>=0);
    assert(Number.isSafeInteger(e.counter)&&e.counter>0);
    assert.equal(new Set(e.basis).size,e.basis.length);
    const basisSet=new Set(e.basis);
    for(const dep of e.basis) for(const transitive of done.get(dep).basis) assert(basisSet.has(transitive),'basis must be downward closed');
    const total=sorted(records.filter(r=>receiverBasis || basisSet.has(r.event)));
    const visibleSet=new Set(e.visible);
    assert.equal(visibleSet.size,e.visible.length);
    const view=total.filter(r=>visibleSet.has(r.id));
    assert.equal(view.length,visibleSet.size,'unknown visible occurrence');
    assert(Number.isSafeInteger(e.gap)&&e.gap>=0&&e.gap<=view.length);
    const left=e.gap?view[e.gap-1]:null;
    const right=visibleRight?view[e.gap]??null:total[ left?total.findIndex(r=>r.id===left.id)+1:0 ]??null;
    let lo=left?.key??[];const hi=right?.key??null;
    assert(typeof e.text==='string' && e.text.isWellFormed(),'Unicode scalar string');
    const scalars=[...e.text];assert(scalars.length>0,'nonempty run');
    for(let i=0;i<scalars.length;i++) {
      const key=between(lo,hi,[e.writer,e.counter,i]);
      records.push({id:elementId(e,i),event:id,scalar:scalars[i],key});lo=key;
    }
    done.set(id,e);
  }
  const result=sorted(records);
  assert.equal(new Set(result.map(r=>r.id)).size,result.length);
  for(let i=1;i<result.length;i++)assert(compare(result[i-1].key,result[i].key)<0,'key collision');
  return result;
}
export const ids=events=>interpret(events).map(r=>r.id);
export const render=(events,visible=null,options={})=>interpret(events,options).filter(r=>visible===null || new Set(visible).has(r.id)).map(r=>r.scalar).join('');
export const keys=events=>interpret(events).map(r=>[r.id,r.key]);
