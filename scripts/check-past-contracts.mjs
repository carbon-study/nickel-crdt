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
      'Nickel.EventGraph.membership_is_exact','', 'membership_is_exact'],
    // Migration: has_event's scan rule now belongs to the generic owner.
    // Test its concrete caller's callee and exact callback bridge separately,
    // with both native membership bodies withheld by the existing assertion.
    ['past-membership-without-generic-contract',
      /  Graph\.membership_is_exact[^\n]+;\n/,
      'Nickel.EditPast.event_membership_is_exact','', 'event_membership_is_exact'],
    ['past-membership-without-concrete-bridge',
      /  assert \(Shared\.has_id[^\n]+;\n/,
      'Nickel.EditPast.event_membership_is_exact','', 'event_membership_is_exact'],
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
    // Two-receiver past selection: every link is load-bearing for its own owner.
    ['past-shared-path-without-edge-step', /  ancestor_follows_edge into roots start next;\n/, 'Nickel.EditPastTotal.shared_path_stays_shared'],
    ['past-shared-path-without-other-edge-step', /  ancestor_follows_edge other roots start next;\n/, 'Nickel.EditPastTotal.shared_path_stays_shared'],
    ['past-shared-path-without-recursion', /  shared_path_stays_shared into other roots next rest finish;\n/, 'Nickel.EditPastTotal.shared_path_stays_shared'],
    ['past-agreement-without-path-transfer', /    shared_path_stays_shared into other roots root steps id;\n/, 'Nickel.EditPastTotal.shared_ancestry_agrees'],
    ['past-path-end-without-recursion', /  path_end_is_present facts next rest finish;\n/, 'Nickel.EditPastTotal.path_end_is_present'],
    ['past-ancestor-presence-without-path', /    path_end_is_present facts root steps id;\n/, 'Nickel.EditPastTotal.ancestor_is_present'],
    ['past-unique-facts-without-positions', /unique_slice_nat_positions \(Alloc\.Vec\.impl_1__as_slice facts\) i j in\n/, 'Nickel.EditPastTotal.unique_present_facts_agree', '() in\n'],
    ['past-whole-facts-without-presence', /    ancestor_is_present into roots id;\n/, 'Nickel.EditPastTotal.whole_facts_give_shared_ancestry'],
    ['past-whole-facts-without-uniqueness', /unique_present_facts_agree other fact stored in\n/, 'Nickel.EditPastTotal.whole_facts_give_shared_ancestry', '() in\n'],
    ['past-selection-without-agreement', /  shared_ancestry_agrees into other roots;\n/, 'Nickel.EditPastTotal.shared_ancestry_selects_same_past'],
    ['past-selection-without-other-exactness', /  successful_past_is_exact_closure other roots;\n/, 'Nickel.EditPastTotal.shared_ancestry_selects_same_past'],
    ['past-receivers-without-whole-facts', /  whole_facts_give_shared_ancestry into other roots;\n/, 'Nickel.EditPastTotal.two_closed_receivers_select_same_past'],
    ['past-receivers-without-other-totality', /  causally_closed_history_computes_exact_past other roots;\n/, 'Nickel.EditPastTotal.two_closed_receivers_select_same_past'],
    ['past-receivers-without-selection', /  shared_ancestry_selects_same_past into other roots;\n/, 'Nickel.EditPastTotal.two_closed_receivers_select_same_past'],
  ];
  for(const [control,pattern,theorem,replacement='',scope] of controls) {
    const name=theorem.split('.').slice(0,2).join('.')+'.fst';
    const original=await fs.readFile(path.join(proof,name),'utf8');
    let start=0,end=original.length;
    if(scope) {
      const declaration=new RegExp('^let (?:rec )?'+scope+' ','m').exec(original);assert(declaration,control+' declaration');
      start=declaration.index;
      const next=/\nlet (?:rec )?\w+ /.exec(original.slice(start+declaration[0].length));
      end=next?start+declaration[0].length+next.index:original.length;
    }
    const body=original.slice(start,end);
    assert.equal([...body.matchAll(new RegExp(pattern.source,pattern.flags.includes('g')?pattern.flags:pattern.flags+'g'))].length,1,control+' anchor must be unique');
    const dir=path.join(path.dirname(proof),control);
    await fs.rm(dir,{recursive:true,force:true});
    await fs.cp(proof,dir,{recursive:true,preserveTimestamps:true});
    let changed=body.replace(pattern,replacement);
    if(control==='past-membership-without-generic-contract') {
      // Also withhold the callee's automatic SMT-pattern route.
      const anchor='    Tactics.prune "Nickel_crdt.Edit.has_event";';
      assert.equal(changed.split(anchor).length,2,control+' callee-prune anchor');
      changed=changed.replace(anchor,anchor+'\n    Tactics.prune "Nickel.EventGraph.membership_is_exact";');
    }
    const view=original.slice(0,start)+changed+original.slice(end);await put(path.join(dir,name),view);
    const result=await verify({dir,roots:[path.join(dir,name)],fstar,models,modelCache});
    await fs.writeFile(path.join(output,control+'.proof.log'),result.log);
    assert(hasOrdinaryTheoremRejection({status:result.status,log:result.log,theorem,view}),
      'require ordinary owning theorem rejection for '+control+': '+result.log);
    console.log('PASS '+control+': source/loop contract is load-bearing');
  }
}
