// This adapter consumes real Python effect facts. It does not implement Undo.
import assert from 'node:assert/strict';
import fs from 'node:fs';
import {interpret, keys} from '../ordered-gap-reference/order.mjs';
import {treeInterpret, expandTree} from '../ordered-gap-reference/tree.mjs';
assert(process.argv[2], 'supply the actual trace.py output file');
const input=JSON.parse(fs.readFileSync(process.argv[2],'utf8'));
assert.equal(input.format,'order-effect-bridge-1');
let views=0, effectControls=0, wholeGapControls=0;
const receipts=[];
for(const trace of input.traces) {
  const bySource=new Map(), forward=new Map(), reverse=new Map();
  for(const i of trace.insertions) {
    assert(!bySource.has(i.event));
    const id=`${i.writer}:${i.counter}`;
    i.creates.forEach((birth,n)=>{
      assert(!forward.has(birth));
      const orderId=`${id}/${n}`;
      assert(!reverse.has(orderId));
      forward.set(birth,orderId); reverse.set(orderId,birth);
    });
    bySource.set(i.event,{writer:i.writer,counter:i.counter,text:i.text,
      basis:i.basis,visible:i.visible,gap:i.gap});
  }
  // Bijection only: scalar payloads do not select identities or positions.
  const mapBirth=b=>{assert(forward.has(b),'unknown birth');return forward.get(b);};
  const records=new Map([...bySource].map(([source,i])=>[source,{...i,
    basis:i.basis.map(s=>{assert(bySource.has(s));const x=bySource.get(s);return `${x.writer}:${x.counter}`;}).sort(),
    visible:i.visible.map(mapBirth).sort()}]));
  const steps=[];
  for(const step of trace.steps) {
    const texts={};
    for(const [writer,view] of Object.entries(step.views)) {
      const events=view.facts.filter(f=>f.creates.length).map(f=>{
        assert(records.has(f.id),'birth without authored placement');
        const authored=trace.insertions.find(i=>i.event===f.id);
        assert.deepEqual(f.creates,authored.creates,'birth identities changed');
        assert.deepEqual(f.payloads,authored.creates.map((birth,n)=>[birth,[...authored.text][n]]),'payload/identity pair changed');
        return records.get(f.id);
      });
      const order=interpret(events), visible=new Set(view.visible.map(mapBirth));
      assert.equal(order.length,view.facts.reduce((n,f)=>n+f.creates.length,0),'no rebirth on Undo/Restore');
      const selected=order.filter(r=>visible.has(r.id));
      assert.equal(selected.length,visible.size,'effect names unplaced birth');
      const text=selected.map(r=>r.scalar).join('');
      assert.equal(text,view.expected,`${trace.name}: ${step.label}: ${writer}`);
      assert.deepEqual(expandTree(treeInterpret(events)),keys(events),'tree bridge');
      // Cold order reconstruction and a different insertion delivery order.
      assert.deepEqual(keys(JSON.parse(JSON.stringify(events)).reverse()),keys(events));
      const allText=order.map(r=>r.scalar).join('');
      if(allText!==view.expected) effectControls++;
      const wrong=interpret(events,{visibleRight:true}).filter(r=>visible.has(r.id)).map(r=>r.scalar).join('');
      if(wrong!==view.expected) wholeGapControls++;
      texts[writer]=text; views++;
    }
    steps.push({label:step.label,texts});
  }
  receipts.push({name:trace.name,steps});
}
assert(effectControls>0,'dropping real effect filtering must fail');
assert(wholeGapControls>0,'visible-right mutation must fail after real withdrawal/redo');
console.log(JSON.stringify({traces:receipts,views,effectControls,wholeGapControls},null,2));
