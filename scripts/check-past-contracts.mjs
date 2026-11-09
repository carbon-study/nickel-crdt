// Load-bearing connections for the new actual-past soundness boundary.
import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import path from 'node:path';
import {put,verify} from './proof-cache.mjs';
import {hasOrdinaryTheoremRejection} from './negative-proof-evidence.mjs';
export async function checkPastContracts({proof,output,fstar,models,modelCache}) {
  const controls=[
    ['past-membership-without-loop-rule',
      /  Nickel\.LoopUtil\.preserve_any[^\n]+;\n/,
      'Nickel.EditPast.event_membership_is_exact'],
    ['past-membership-without-pattern',
      /(?<=let event_membership_is_exact[^\n]*) \[SMTPat \(Native\.has_event ids id\)\]/,
      'Nickel.EditPast.extend_past_preserves'],
    ['past-ancestors-without-source-contract',
      /  past_stays_in_closed_set[^\n]+;\n/,
      'Nickel.EditPast.past_has_only_ancestors_and_keeps_roots'],
    ['past-depth-without-pass-contract',
      /    past_pass_covers_edges[^\n]+;\n/,
      'Nickel.EditPast.past_covers_bounded_predecessor_paths'],
    ['past-paths-without-depth-contract',
      /  past_covers_bounded_predecessor_paths[^\n]+;\n/,
      'Nickel.EditPast.past_contains_short_paths'],
    ['past-every-path-without-shortening',
      /  every_path_has_short_path[^\n]+;\n/,
      'Nickel.EditPast.past_contains_every_causal_path'],
    ['past-exact-without-path-contract',
      /^ +past_contains_every_causal_path[^\n]+;\n/m,
      'Nickel.EditPast.successful_past_is_exact_closure'],
    ['past-roots-without-presence-pattern', /(?<=let stored_id_presence_agrees[^\n]*) \[SMTPat \(fact_id_present facts id\)\]/, 'Nickel.EditPastTotal.stored_roots_are_present'],
    ['past-unique-rejects-impossible-predicate', /(?<=let unique_selection[^\n]+\n)  forall[^\n]+/, 'Nickel.EditPastTotal.empty_and_singleton_roots_are_unique',
      '  forall(i: nat) (j: nat). Prims.l_and (Prims.l_and (i < Seq.length ids) (j < Seq.length ids)) (Seq.index ids i == Seq.index ids j ==> i == j)'],
    ['past-push-without-room', /  missing_stored_id_leaves_room[^\n]+;\n/, 'Nickel.EditPastTotal.fresh_stored_push_succeeds'],
    ['past-extend-without-total-push', /^ +fresh_stored_push_succeeds[^\n]+;\n/m, 'Nickel.EditPastTotal.extend_stored_selection_succeeds'],
    ['past-pass-without-total-extend', /^ +extend_stored_selection_succeeds[^\n]+;\n/m, 'Nickel.EditPastTotal.stored_pass_succeeds'],
    ['past-total-without-total-pass', /^ +stored_pass_succeeds[^\n]+;\n/m, 'Nickel.EditPastTotal.fitting_closed_history_computes_past'],
    ['past-exact-without-totality', /  fitting_closed_history_computes_past[^\n]+;\n/, 'Nickel.EditPastTotal.fitting_past_is_total_and_exact'],
    ['past-scan-without-exact-law', /  duplicate_scan_is_exact roots;\n/, 'Nickel.EditPastTotal.scanned_roots_compute_exact_past'],
  ];
  for(const [control,pattern,theorem,replacement=''] of controls) {
    const name=theorem.split('.').slice(0,2).join('.')+'.fst';
    const original=await fs.readFile(path.join(proof,name),'utf8');
    assert.equal([...original.matchAll(new RegExp(pattern.source,pattern.flags.includes('g')?pattern.flags:pattern.flags+'g'))].length,1,control+' anchor must be unique');
    const dir=path.join(path.dirname(proof),control);
    await fs.rm(dir,{recursive:true,force:true});
    await fs.cp(proof,dir,{recursive:true,preserveTimestamps:true});
    const view=original.replace(pattern,replacement);await put(path.join(dir,name),view);
    const result=await verify({dir,roots:[path.join(dir,name)],fstar,models,modelCache});
    await fs.writeFile(path.join(output,control+'.proof.log'),result.log);
    assert(hasOrdinaryTheoremRejection({status:result.status,log:result.log,theorem,view}),
      'require ordinary owning theorem rejection for '+control+': '+result.log);
    console.log('PASS '+control+': source/loop contract is load-bearing');
  }
}
