// Existing candidate order only. Python retains the real effect interpreter.
import readline from 'node:readline';
import {interpret} from '../ordered-gap-reference/order.mjs';
for await (const line of readline.createInterface({input:process.stdin})) {
  try {
    const {events,visible}=JSON.parse(line), records=interpret(events), seen=new Set(visible);
    if(records.filter(r=>seen.has(r.id)).length!==seen.size) throw Error('unplaced visible birth');
    console.log(JSON.stringify({ok:true,text:records.filter(r=>seen.has(r.id)).map(r=>r.scalar).join(''),
      ids:records.map(r=>r.id),digits:records.reduce((n,r)=>n+r.key.length,0)}));
  } catch(e) {console.log(JSON.stringify({ok:false,error:String(e.message)}));}
}
