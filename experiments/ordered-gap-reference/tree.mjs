// A separately traversed, prefix-sharing representation of order.mjs's keys.
// This is order-only research; no visibility/effect semantics are added.
import assert from 'node:assert/strict';
import {eventId,elementId} from './order.mjs';
function digitCompare(a,b){for(let i=0;i<4;i++)if(a[i]!==b[i])return a[i]<b[i]?-1:1;return 0;}
function preorder(nodes) {
  const children=new Map();
  for(const n of nodes){if(!children.has(n.parent))children.set(n.parent,[]);children.get(n.parent).push(n);}
  for(const values of children.values())values.sort((a,b)=>digitCompare(a.digit,b.digit));
  const stack=[...(children.get(null)??[])].reverse(),out=[];
  while(stack.length){const n=stack.pop();out.push(n);for(const child of [...(children.get(n.id)??[])].reverse())stack.push(child);}
  assert.equal(out.length,nodes.length,'all nodes must be rooted');
  return out;
}
export function treeInterpret(events) {
  const nodes=[],done=new Map(),pending=JSON.parse(JSON.stringify(events));
  while(pending.length){const at=pending.findIndex(e=>e.basis.every(id=>done.has(id)));assert(at>=0,'missing/cyclic dependency');
    const [e]=pending.splice(at,1),id=eventId(e);
    if(done.has(id)){assert.deepEqual(done.get(id),e);continue;}
    assert(Number.isSafeInteger(e.writer)&&e.writer>=0&&Number.isSafeInteger(e.counter)&&e.counter>0);
    const basis=new Set(e.basis);assert.equal(basis.size,e.basis.length);
    for(const dep of e.basis)for(const transitive of done.get(dep).basis)assert(basis.has(transitive));
    const total=preorder(nodes.filter(n=>basis.has(n.event))),seen=new Set(e.visible);
    assert.equal(seen.size,e.visible.length);
    const visible=total.filter(n=>seen.has(n.id));assert.equal(visible.length,seen.size);
    assert(Number.isSafeInteger(e.gap)&&e.gap>=0&&e.gap<=visible.length);
    const left=e.gap?visible[e.gap-1]:null;
    const right=total[left?total.findIndex(n=>n.id===left.id)+1:0]??null;
    // A whole-order successor under left is its first immediate child.
    let height=right && right.parent===(left?.id??null)?right.digit[0]-1:0;
    assert(Number.isSafeInteger(height));
    assert(typeof e.text==='string'&&e.text.isWellFormed()&&e.text.length>0);
    let parent=left?.id??null;
    for(const [index,scalar] of [...e.text].entries()){
      const n={id:elementId(e,index),event:id,scalar,parent,digit:[height,e.writer,e.counter,index]};
      nodes.push(n);parent=n.id;height=0;
    }
    done.set(id,e);
  }
  return preorder(nodes);
}
// Diagnostic abstraction, not stored position paths. It intentionally expands
// shared prefixes to compare with the deliberately expensive key reference.
export function expandTree(nodes) {
  const paths=new Map();
  return nodes.map(n=>{const key=[...(n.parent===null?[]:paths.get(n.parent)),n.digit];paths.set(n.id,key);return[n.id,key];});
}
