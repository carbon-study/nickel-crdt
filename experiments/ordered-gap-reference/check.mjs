import assert from 'node:assert/strict';
import {author,interpret,ids,render,keys,eventId} from './order.mjs';
import {treeInterpret,expandTree} from './tree.mjs';
function refinement(events){assert.deepEqual(expandTree(treeInterpret(events)),keys(events),'tree-to-key abstraction');}
const receipt={witnesses:{},deliveryOrders:0,generatedSnapshots:0,controls:{}};
function expect(name,events,visible,text){refinement(events);assert.equal(render(events,visible),text,name);receipt.witnesses[name]=text;}
const root=author([],0,1,'ab',[],0),ab=[root],base=ids(ab),[a,b]=base;
const x=author(ab,1,1,'X',[b],0);
expect('q30-after-return',[root,x],null,'Xab');
expect('q31-after-return',[root,x],null,'Xab'); // same current visible gap, not a saved-cursor implementation
const peer=author(ab,1,1,'X',base,1);
expect('peer-insertion-survives-withdrawal',[root,peer],[`${eventId(peer)}/0`],'X');
expect('peer-insertion-after-return',[root,peer],null,'aXb');
const longer=author([],0,1,'abcdef',[],0),six=ids([longer]);
const xy=author([longer],1,1,'XY',[six[0],six[4],six[5]],1);
expect('longer-hidden-middle',[longer,xy],null,'aXYbcdef');
const friday=author([],0,1,'Friday!',[],0),fridayIds=ids([friday]);
const monday=author([friday],1,1,'Monday',[fridayIds.at(-1)],0);
expect('replacement-before-return',[friday,monday],[...ids([monday,friday]).filter(id=>id.startsWith('1:')),fridayIds.at(-1)],'Monday!');
expect('replacement-after-return',[friday,monday],null,'MondayFriday!');
const hiddenX=author(ab,1,1,'X',base,1),afterX=[root,hiddenX];
const y=author(afterX,2,1,'Y',base,1);
expect('previously-inserted-hidden-run',[...afterX,y],null,'aYXb');
assert.equal(render([...afterX,y],null,{visibleRight:true}),'aXYb');
receipt.controls.visibleRightOnly='rejects required aYXb: produces aXYb';
function* permutations(xs){if(!xs.length){yield [];return;}for(let i=0;i<xs.length;i++)for(const tail of permutations(xs.filter((_,j)=>j!==i)))yield[xs[i],...tail];}
function legal(order){const known=new Set();for(const e of order){if(!e.basis.every(id=>known.has(id)))return false;known.add(eventId(e));}return true;}
for(const swap of [false,true]) {
  const p=author(ab,swap?2:1,1,'XY',base,1),q=author(ab,swap?1:2,1,'PQ',base,1),initial=[root,p,q];
  const text=swap?'aPQXYb':'aXYPQb';
  expect(`concurrent-runs-${swap}`,initial,null,text);
  const internal=author(initial,0,2,'Z',ids(initial),2),history=[...initial,internal];
  // Explicit later insertion into a run is allowed to split that run.
  expect(`later-internal-insertion-${swap}`,history,null,swap?'aPZQXYb':'aXZYPQb');
  const canonical=keys(history);
  for(const order of permutations(history))if(legal(order)){
    assert.deepEqual(keys(order),canonical);refinement(order);refinement([...order,order[0]]);refinement(JSON.parse(JSON.stringify(order)));
    assert.deepEqual(keys([...order,order[0]]),canonical,'duplicate');
    assert.deepEqual(keys(JSON.parse(JSON.stringify(order))),canonical,'cold');
    receipt.deliveryOrders++;
  }
}
const p=author(ab,1,1,'XY',base,1),q=author(ab,2,1,'PQ',base,1);
assert.notEqual(render([root,p,q],null,{receiverBasis:true}),render([root,q,p],null,{receiverBasis:true}));
receipt.controls.receiverRechoosesBounds='rejects convergence: second arrival goes first';
// Bounded insertion/visibility exploration. This is not an undo oracle.
let frontier=[ab];
for(let depth=0;depth<3;depth++) {
  const next=[];
  for(const events of frontier){const before=interpret(events),n=before.length;
    for(let mask=0;mask<2**n;mask++){
      const visible=before.filter((_,i)=>mask&(2**i)).map(r=>r.id);
      for(let gap=0;gap<=visible.length;gap++){
        const event=author(events,1,depth+1,depth%2?'UV':'x',visible,gap),result=[...events,event],after=interpret(result);
        const oldMap=new Map(before.map(r=>[r.id,r.key]));
        for(const r of after)if(oldMap.has(r.id))assert.deepEqual(r.key,oldMap.get(r.id),'old key moves');
        const displayed=render(result,[...visible,...after.filter(r=>r.event===eventId(event)).map(r=>r.id)]);
        const oldView=before.filter(r=>visible.includes(r.id)).map(r=>r.scalar);
        assert.equal(displayed,[...oldView.slice(0,gap),event.text,...oldView.slice(gap)].join(''),'visible gap');
        assert.deepEqual(keys(JSON.parse(JSON.stringify(result))),keys(result));refinement(result);refinement(JSON.parse(JSON.stringify(result)));receipt.generatedSnapshots++;
        // Keep all depth-one cases, then a deterministic bounded cross-section.
        if(depth===0 || (mask===0&&gap===0) || (mask===2**n-1&&gap===visible.length))next.push(result);
      }
    }
  }
  frontier=next;
}
const growth=[];let sequential=[];
for(let i=0;i<32;i++){sequential.push(author(sequential,0,i+1,'x',ids(sequential),i));if([0,7,15,31].includes(i)){const r=interpret(sequential);growth.push({scalars:r.length,totalKeyDigits:r.reduce((n,x)=>n+x.key.length,0),storedTreeDigits:treeInterpret(sequential).length,maxKeyDepth:Math.max(...r.map(x=>x.key.length))});}}
assert.deepEqual(growth.map(x=>x.totalKeyDigits),[1,36,136,528]);assert.deepEqual(growth.map(x=>x.storedTreeDigits),[1,8,16,32]);receipt.appendGrowth=growth;
console.log(JSON.stringify(receipt,null,2));
