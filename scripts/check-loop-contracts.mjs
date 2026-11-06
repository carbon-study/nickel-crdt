// Dependency controls for the plain-loop contracts; no Rust changes here.
import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import path from 'node:path';
import {put,verify} from './proof-cache.mjs';
import {hasOrdinaryTheoremRejection} from './negative-proof-evidence.mjs';
function declaration(view,name) {
  const match=new RegExp('^let (?:rec )?'+name+' ','m').exec(view);assert(match,'missing declaration '+name);
  const start=match.index,rest=view.slice(start+match[0].length);
  const next=/\nlet (?:rec )?\w+ /.exec(rest);
  return [start,next?start+match[0].length+next.index:view.length];
}
function removeCall(view,name,needle) {
  const [a,b]=declaration(view,name),body=view.slice(a,b);
  assert.equal(body.split(needle).length,2,'control anchor must occur once in '+name);
  return view.slice(0,a)+body.replace(needle,'')+view.slice(b);
}
export async function checkLoopContracts({proof,output,fstar,models,modelCache}) {
  const loop='Nickel.LoopUtil.fst',smoke='Nickel.Smoke.fst';
  const originals=new Map(await Promise.all([loop,smoke].map(async name=>[name,await fs.readFile(path.join(proof,name),'utf8')])));
  const cases=[
    ['loop-no-step',loop,'plain_preserve','plain_step start finish inv value f;'],
    ['loop-no-end',loop,'plain_preserve','plain_end start finish inv value f;'],
    ['loop-no-induction',loop,'plain_preserve','plain_preserve (start +! mk_int 1) finish inv (f value start) f p post;'],
    ['loop-no-adapter',loop,'plain_preserve_any','plain_preserve start finish inv value f p post;'],
    ['interpret-no-adapter',loop,'plain_interpret_any','plain_interpret start finish inv value f next stop done;'],
    ['interpret-no-fold-step',loop,'plain_interpret','plain_step start finish inv value f;'],
    ['interpret-no-option-step',loop,'plain_interpret','option_run_step finish start value next stop done;'],
    ['interpret-no-fold-end',loop,'plain_interpret','plain_end start finish inv value f;'],
    ['interpret-no-induction',loop,'plain_interpret','plain_interpret (start +! mk_int 1) finish inv (f value start) f next stop done;'],
    ['native-no-first-parity',smoke,'flip_involution','flip_exact n value;'],
    ['native-no-second-parity',smoke,'flip_involution','flip_exact n (Nickel_proof_smoke.flip n value);'],
    ['native-no-interpret',smoke,'flip_bridge','Nickel.LoopUtil.plain_interpret_any (mk_usize 0) n (flip_next n) keep identity;'],
    ['native-no-invariant-rule',smoke,'flip_exact',"Nickel.LoopUtil.plain_preserve_any (mk_usize 0) n (fun at s -> parity s (v n - at) == parity value (v n)) (fun s -> s == parity value (v n));"],
  ];
  for(const [name,file,lemma,needle] of cases) {
    const view=removeCall(originals.get(file),lemma,needle);
    try {
      await put(path.join(proof,file),view);
      const result=await verify({dir:proof,roots:[path.join(proof,file)],fstar,models,modelCache});
      await fs.writeFile(path.join(output,name+'.proof.log'),result.log);
      assert(hasOrdinaryTheoremRejection({status:result.status,log:result.log,theorem:file.slice(0,-4)+'.'+lemma,view}),
        'require ordinary named rejection after removing loop contract: '+result.log);
      console.log('PASS '+name+': contract dependency is load-bearing');
    } finally {
      await put(path.join(proof,file),originals.get(file));
    }
  }
}
// Keep the original bridge control, and independently check the direct parity
// caller without making the old bridge available as a lemma.
export async function checkDirectLoop({proof,output,fstar,models,modelCache,mode}) {
  const file=path.join(proof,'Nickel.Smoke.fst'),original=await fs.readFile(file,'utf8');
  const [a,b]=declaration(original,'flip_bridge'),view=original.slice(0,a)+original.slice(b);
  try {
    await put(file,view);
    const result=await verify({dir:proof,roots:[file],fstar,models,modelCache});
    await fs.writeFile(path.join(output,'direct-parity-'+mode+'.proof.log'),result.log);
    if(mode==='positive')assert.equal(result.status,0,result.log);
    else assert(hasOrdinaryTheoremRejection({status:result.status,log:result.log,theorem:'Nickel.Smoke.flip_exact',view}),
      'require ordinary direct-parity rejection of the actual wrong Rust body: '+result.log);
    console.log('PASS direct parity '+mode+' without the legacy bridge');
  } finally { await put(file,original); }
}
