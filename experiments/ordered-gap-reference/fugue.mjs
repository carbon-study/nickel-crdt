// Authored research interpretation of Weidner/Kleppmann, arXiv:2305.00583v3,
// Algorithm 1 and section 5.3. Visibility is supplied, not an undo algorithm.
import assert from 'node:assert/strict';
import {eventId,elementId} from './order.mjs';
export const ROOT='root';
const copy=x=>JSON.parse(JSON.stringify(x));
function compareId(a,b) {
  const x=a.split(/[:/]/).map(Number),y=b.split(/[:/]/).map(Number);
  for(let i=0;i<3;i++)if(x[i]!==y[i])return x[i]<y[i]?-1:1;
  return 0;
}
class Tree {
  constructor(options={}) {this.options=options;this.nodes=new Map([[ROOT,{id:ROOT,left:[],right:[]}]]);}
  whole() {
    const result=[];
    const visit=id=>{const n=this.nodes.get(id);n.left.forEach(visit);if(id!==ROOT)result.push(n);n.right.forEach(visit);};
    visit(ROOT);return result;
  }
  add(op) {
    assert(!this.nodes.has(op.id),'duplicate node');
    const parent=this.nodes.get(op.parent);assert(parent,'missing parent');
    assert(op.rightOrigin===null||this.nodes.has(op.rightOrigin),'missing right origin');
    const siblings=parent[op.side];assert(siblings,'unknown side');
    let at;
    if(op.side==='right'&&!this.options.plain) {
      const rank=new Map(this.whole().map((n,i)=>[n.id,i]));rank.set(null,Infinity);
      at=siblings.findIndex(id=>{
        const old=this.nodes.get(id);
        return rank.get(op.rightOrigin)>rank.get(old.rightOrigin)||
          (op.rightOrigin===old.rightOrigin&&compareId(op.id,id)<0);
      });
    } else at=siblings.findIndex(id=>compareId(op.id,id)<0);
    siblings.splice(at<0?siblings.length:at,0,op.id);
    this.nodes.set(op.id,{...op,left:[],right:[]});
  }
  insert(id,event,scalar,visible,gap) {
    const all=this.whole(),view=all.filter(n=>visible.has(n.id));
    assert.equal(view.length,visible.size,'unknown visible occurrence');
    assert(Number.isSafeInteger(gap)&&gap>=0&&gap<=view.length,'invalid gap');
    const leftOrigin=gap?view[gap-1].id:ROOT;
    const next=leftOrigin===ROOT?0:all.findIndex(n=>n.id===leftOrigin)+1;
    const rightOrigin=(this.options.visibleRight?view[gap]:all[next])?.id??null;
    const side=this.nodes.get(leftOrigin).right.length?'left':'right';
    const parent=side==='right'?leftOrigin:rightOrigin;
    assert(parent!==null,'missing successor');
    const op={id,event,scalar,leftOrigin,rightOrigin,parent,side};
    this.add(op);return op;
  }
}

// The event contract is the existing order.mjs author() contract. Every origin
// is derived in the author's causal insertion basis, then frozen for integration.
export function fugueInterpret(events,options={}) {
  const pending=[],byId=new Map();
  for(const raw of events) {
    const e=copy(raw),id=eventId(e);
    assert(Number.isSafeInteger(e.writer)&&e.writer>=0,'invalid writer');
    assert(Number.isSafeInteger(e.counter)&&e.counter>0,'invalid counter');
    assert(Array.isArray(e.basis)&&e.basis.every(x=>typeof x==='string'),'invalid basis');
    assert.equal(new Set(e.basis).size,e.basis.length,'duplicate dependency');
    assert(Array.isArray(e.visible)&&e.visible.every(x=>typeof x==='string'),'invalid visible set');
    assert.equal(new Set(e.visible).size,e.visible.length,'duplicate visible occurrence');
    assert(typeof e.text==='string'&&e.text.isWellFormed()&&[...e.text].length>0,'invalid scalar string');
    if(byId.has(id)){assert.deepEqual(byId.get(id),e,'conflicting duplicate');continue;}
    byId.set(id,e);pending.push(e);
  }
  const integrated=[],operations=new Map(),result=new Tree(options);
  while(pending.length) {
    const at=pending.findIndex(e=>e.basis.every(id=>operations.has(id)));
    assert(at>=0,'missing dependency or cycle');
    const [e]=pending.splice(at,1),id=eventId(e),basis=new Set(e.basis);
    for(const dep of e.basis)for(const ancestor of byId.get(dep).basis)
      assert(basis.has(ancestor),'basis must be downward closed');
    const author=new Tree(options);
    for(const dep of integrated)if(options.receiverBasis||basis.has(dep))
      operations.get(dep).forEach(op=>author.add(op));
    const visible=new Set(e.visible),ops=[];
    for(const [i,scalar]of [...e.text].entries()) {
      const op=author.insert(elementId(e,i),id,scalar,visible,e.gap+i);
      ops.push(op);visible.add(op.id);
    }
    operations.set(id,ops);integrated.push(id);ops.forEach(op=>result.add(op));
  }
  // Expose semantic/order metadata, not mutable traversal child arrays.
  return result.whole().map(({left,right,...record})=>record);
}
export const fugueIds=(events,options={})=>fugueInterpret(events,options).map(r=>r.id);
export const fugueRender=(events,visible=null,options={})=>fugueInterpret(events,options)
  .filter(r=>visible===null||new Set(visible).has(r.id)).map(r=>r.scalar).join('');

export function* causalSchedules(events,known=new Set()) {
  if(!events.length){yield [];return;}
  for(const e of events)if(e.basis.every(id=>known.has(id)))
    for(const tail of causalSchedules(events.filter(x=>x!==e),new Set([...known,eventId(e)])))yield [e,...tail];
}
