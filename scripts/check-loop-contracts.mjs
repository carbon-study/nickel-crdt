// Dependency controls for the plain-loop contracts; no Rust changes here.
import assert from 'node:assert/strict';
import {viewUnits} from './text-family-run.mjs';
function declaration(view,name) {
  const match=new RegExp('^let (?:rec )?'+name+' ','m').exec(view);assert(match,'missing declaration '+name);
  const start=match.index,rest=view.slice(start+match[0].length);
  const next=/\nlet (?:rec )?\w+ /.exec(rest);
  return [start,next?start+match[0].length+next.index:view.length];
}
function removeCall(view,name,needle) {
  const [a,b]=declaration(view,name),body=view.slice(a,b);
  assert.equal(body.split(needle).length,2,'control anchor must occur once in '+name);
  return view.slice(0,a)+body.replace(needle,needle.endsWith(';')?'':'()')+view.slice(b);
}
// Smoke's loop-contract controls (#198), as units on the smoke positive workspace (read serves it). In place; each
// unit restores the workspace.
export function loopUnits(read) {
  const loop='Nickel.LoopUtil.fst',smoke='Nickel.Smoke.fst';
  const originals=new Map([loop,smoke].map(name=>[name,read(name)]));
  const cases=[
    ['result-no-return-rule',loop,'result_preserve_any','preserve_any start finish p (fun (s: state) -> successful (done s)) (result_safe successful failed);'],
    ['return-no-step',loop,'preserve','unroll start finish inv value f;'],
    ['return-no-end',loop,'preserve','empty start finish inv value f;'],
    ['return-no-induction',loop,'preserve','preserve (start +! mk_int 1) finish inv next f p post returned'],
    ['return-no-adapter',loop,'preserve_any','preserve start finish inv value f p post returned;'],
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
  return viewUnits('smoke',cases.map(([name,file,lemma,needle])=>({name,files:{[file]:removeCall(originals.get(file),lemma,needle)},roots:[file],
    theorem:file.slice(0,-4)+'.'+lemma,inPlace:true,log:name+'.proof.log',pass:name+': contract dependency is load-bearing',
    failure:'require ordinary named rejection after removing loop contract'})),read);
}
// The direct parity caller without the legacy bridge: it must verify on the healthy extraction (mode "positive") and be
// rejected at flip_exact on the wrong-loop extraction. Same mutated view in both workspaces.
export function directParityUnits(read,mode) {
  const file='Nickel.Smoke.fst',original=read(file);
  const [a,b]=declaration(original,'flip_bridge'),view=original.slice(0,a)+original.slice(b);
  const c={name:'direct-parity-'+mode,files:{[file]:view},roots:[file],inPlace:true,log:'direct-parity-'+mode+'.proof.log',pass:'direct parity '+mode+' without the legacy bridge'};
  return viewUnits('smoke',[mode==='positive'?{...c,expect:'verify',failure:'direct parity positive must verify'}
    :{...c,theorem:'Nickel.Smoke.flip_exact',failure:'require ordinary direct-parity rejection of the actual wrong Rust body'}],read);
}

// Actual scalar validator boundaries must use the fallible invariant rule.
export function scalarUnits(read) {
  const file='Nickel.EditWellFormed.fst',original=read(file);
  const units=[];
  for(const lemma of ['scalar_validation_is_sound','valid_scalar_input_succeeds']) {
    const [a,b]=declaration(original,lemma),body=original.slice(a,b);
    const calls=body.match(/Nickel\.LoopUtil\.result_preserve_any[^;]+;/g);
    assert.equal(calls?.length,1,'one fallible rule call at '+lemma);
    const view=removeCall(original,lemma,calls[0]);
    units.push({name:lemma,files:{[file]:view},roots:[file],theorem:'Nickel.EditWellFormed.'+lemma,inPlace:true,
      log:lemma+'.without-rule.proof.log',pass:lemma+': actual validator requires the fallible invariant rule',failure:'require ordinary scalar contract-dependency rejection'});
  }
  return viewUnits('scalar',units,read);
}
