// Ordering only. Python retains the real effect interpreter and joint commit.
import readline from 'node:readline';
import {interpret} from '../ordered-gap-reference/order.mjs';
import {fugueInterpret} from '../ordered-gap-reference/fugue.mjs';
const backend=process.argv[2]==='--fugue'?'fugue':'dense';
for await (const line of readline.createInterface({input:process.stdin})) {
  try {
    const {events,visible}=JSON.parse(line), records=(backend==='fugue'?fugueInterpret:interpret)(events), seen=new Set(visible);
    if(records.filter(r=>seen.has(r.id)).length!==seen.size) throw Error('unplaced visible birth');
    console.log(JSON.stringify({ok:true,backend,text:records.filter(r=>seen.has(r.id)).map(r=>r.scalar).join(''),
      ids:records.map(r=>r.id),...(backend==='dense'?
        {digits:records.reduce((n,r)=>n+r.key.length,0)}:
        {links:records.length*3})})); // parent, left origin, right origin (sentinels occupy slots too)
  } catch(e) {console.log(JSON.stringify({ok:false,error:String(e.message)}));}
}
