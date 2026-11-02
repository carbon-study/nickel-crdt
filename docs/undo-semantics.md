# local undo: decisions, candidate and missing argument

**revision direction:** [the response-led PR plan](response-plan.md) now takes priority over the earlier writer-exclusive activity recommendation. Ren requests restoration of another writer’s deletion and corresponding undo-history adjustment. His later clarification selects own-action Undo plus an explicit, undoable Restore command; the [restricted session profile](private-session-profile.md) records it. This does not reinstate writer-exclusive effects. That behavior still needs a complete trace semantics; the older candidate below is retained for comparison, not adopted.

**Research/design analysis, not an implementation claim.** Nickel has no undo algorithm or undo correctness theorem. Restricting a stack to local commands does not establish the meaning or correctness of its undo. This document identifies the gap rather than treating the activity proposal as solved local undo.

## 1. four separate questions

1. **Selection:** which command/item does this session choose? Local last-in-first-out selection differs from choosing any local item or any remote item.
2. **Effect:** deactivate that command's contributions, restore its previous observed state, or also hide dependent contributions? The same local stack can drive any of these meanings.
3. **Replication:** what new event communicates the decision, and how do causally later and concurrent decisions combine?
4. **Continuation:** what do redo, later edits, delayed children and cold reload do with that event?

A definition that answers only selection is not enough. Nor is a convergent Boolean activity register alone a proof of sequence undo. The required order interpretation and later-command behavior remain to be supplied.

## 2. the literature selects different meanings

The bibliography and exact reading limits are in [the overview](carbon-contract.md#references). This is a focused comparison, not an exhaustive survey or a reproduction of paper implementations.

| source | relevant mechanism | what it does not establish for Nickel |
| --- | --- | --- |
| [Weiss/Urso/Molli 2010, §§5–6](https://doi.org/10.1109/TPDS.2009.173) | ordered line identities, patch degrees and visibility accounting for overlapping deletions | our scalar-gap ordering, single-author activity chain, grouping/children or stack policy |
| [Yu/André/Ignat 2015, §§3–6](https://members.loria.fr/CIgnat/files/pdf/YuDAIS15.pdf) | string-operation descriptors and transitive ground dependencies, with dependent visibility | retaining an independent peer insertion when its ground is undone; §6 does not give a formal proof |
| [Yu/Elvinger/Ignat 2019, §5](https://doi.org/10.4230/LIPIcs.OPODIS.2019.14) | concurrent undo equivalence and causal supersession, represented by undo lengths | a local history-selection policy or the complete sequence interpretation we need |
| [Stewen/Kleppmann 2024, §§2–5](https://arxiv.org/pdf/2404.11308) | local stacks plus RestoreOps that recover register states through operation history | a verified sequence algorithm preserving our placement and independent-insertion requirements |
| [Dolan 2020, §2](https://arxiv.org/pdf/2006.10494) | characterization under an abstract-state-return undoability axiom | an impossibility result for every history-retaining visible-projection restoration design |

### groupware prior art

[Prakash and Knister (1994)](https://web.eecs.umich.edu/~aprakash/papers/undo-tochi94.pdf) already separate selection, shifted targets and dependency conflicts (§3). Their application supplies Conflict, Transpose and Inverse (§4.2). State-preserving transposition alone is insufficient: they also require counterfactual meaning and compatibility with inverse pairs. Section 8.1 exhibits incorrect restoration order after relaxing adjacency conflicts, then introduces ordered locators that can distinguish gaps at the same visible position. Their correctness result is conditional on the supplied laws, not a theorem for arbitrary editing primitives.

For Nickel, this makes historical gap evidence and cancellation compatibility explicit obligations rather than new problems discovered here. We have not supplied the corresponding laws or implementation. Their conflict refusal is a policy option, not automatically our policy of retaining independent peer text. The counterfactual transformed operation must itself be defined; “as if my edit never happened” does not define later dependent edits. Their §7.3 also presents partial versus collective multi-operation undo as a choice; Nickel currently proposes atomic calls.

Reading: §§3, 4.1–4.2, §5.3 Lemma 6 and theorem statement/proof, §§7.3 and 8.1. Other lemmas/algorithms were not audited and no DistEdit implementation was run. Sun's 2002 concurrent-inverse article, Ressel/Gunzenhäuser 1999 and Abowd/Dix 1992 remain reviewer-suggested leads; they are not evidence used by this revision.

### deployed APIs and retained failure witnesses

[Yjs's UndoManager documentation](https://docs.yjs.dev/api/undo-manager) specifies tracked origins, a 500 ms default capture window, explicit capture breaks and stack-item metadata. These are useful selection/grouping precedents. They do not establish our exact target, identity, invisible-activity or continuation laws. The numerical overlap with an editor's chosen 500 ms policy does not establish where that policy came from.

[Loro's undo documentation](https://loro.dev/docs/advanced/undo) describes local-only tracking for one peer, clearing stacks on peer-ID change, configurable grouping, and cursor transformation for elements recreated by undo. This describes the documented interface, not acceptance of Nickel's witnesses.

The following are retained native-fork observations, not fresh executions or claims about current upstream releases. Dark/Loro remain parked. Source and evidence are pinned to [the retained fork](https://github.com/romdotdog/loro/tree/b4bf8191de47019a0dedd5d0ba143cd2cf191185).

| witness | retained result and scope | Nickel obligation |
| --- | --- | --- |
| delivery partition | ordinary List undo gives sax/asx for batch/incremental delivery of the same operations and same pre-undo source/version; each resulting history converges after its own undo is synced | V4 must include subsequent local history behavior, not only convergence after operations are fixed |
| historical side | two Text histories have the same projected import diff and visible sb, but require sab versus asb on restoration under the earlier differing-placement policy (the oracle this experiment tested; superseded for the before/after-a scenario by Ren's 2026-11-02 decision, see §4) | V6 needs historical placement evidence, not projected indices |
| invisible retirement | experimental identity manager consumes B's hidden creation without a new replicated event; a later undo reveals B where the proposed oracle requires empty, and cold reconstruction has no retirement to recover | V5/V8 need an observable semantic event if this candidate policy is adopted |

[Delivery/placement fixture](https://github.com/romdotdog/loro/blob/b4bf8191de47019a0dedd5d0ba143cd2cf191185/crates/loro/tests/undo_delivery_review.rs), [retained replay contract](https://github.com/romdotdog/loro/blob/b4bf8191de47019a0dedd5d0ba143cd2cf191185/scripts/undo-issue-repros/README.md), [retirement evidence](https://github.com/romdotdog/loro/blob/b4bf8191de47019a0dedd5d0ba143cd2cf191185/context/undo-trigger-lifecycle.md). The opt-in planner repairs the selected first two witnesses; it still lacks the third activity boundary. Ordinary delivery dependence is not demonstrated divergence of one common operation set. These distinctions matter more than a generic claim that an engine's undo is broken.

### a worked register distinction

In Stewen/Kleppmann's Fig. 1(d), take a black register, A sets red, then B sets green. Undo by A restores black; redo restores green. In their algorithm, undo's RestoreOp anchors A's set and resolves that anchor's predecessors; redo anchors the undo and resolves its predecessors. It is not equivalent to changing A's set from active to inactive. Their Fig. 3 further has B undo after A undo, revealing red. This is a substantive semantic difference, not different stack bookkeeping. [§§2, 4–5, 7](https://arxiv.org/pdf/2404.11308).

Under a separate, *hypothetical* winner-among-active-writes model, deactivating A leaves B's green; deactivating B afterwards exposes the initial black. This is our comparison, not that paper's algorithm. Therefore “only undo local items” cannot be used to claim compatibility with its restoration semantics. Nickel's future register policy is still open.

### a worked concurrent-toggle distinction

Yu/Elvinger/Ignat's §5.1 compares two concurrent undos of one addition and a redo after one of them. Their semantics coalesces equivalent undos; the later redo prevails. Counting messages modulo two or counting undos versus redos is not equivalent. Nickel's proposed single-origin chain excludes concurrent authorized toggles of the *same command*. That narrows the problem; it does not solve arbitrary selective undo. [§5, Lemma 6](https://doi.org/10.4230/LIPIcs.OPODIS.2019.14).

### dependency is a product choice

Yu/André/Ignat treat operations built on an undone ground as groundless by default, including late concurrent arrival. They also discuss user overrides. Nickel's proposed independent-X witness instead retains X after its surrounding insertion is undone, unless membership was explicitly declared as a child. That is a different rule, not an automatic consequence of calling both systems CRDTs. [§§3–6](https://members.loria.fr/CIgnat/files/pdf/YuDAIS15.pdf).

## 3. exactly what the activity proposal can say

The following is conditional mathematical reasoning about a restricted reference model. It is not a mechanized theorem or a chosen sequence algorithm.

Suppose a finite admitted history H supplies:

- a fixed element order `O(H)`, independent of the current activity map;
- exactly one creating command `c(e)` for each element;
- immutable deletion target sets, with `D(e)` the commands whose deletions target e;
- explicit command membership, including children, and an activity map A.

Define

```
visible_A(e) = A(c(e)) and every d in D(e) has A(d) = false
P(H,A)      = O(H) filtered by visible_A, retaining logical identities
```

For a *fixed H*, changing A for command q cannot change visibility of e if q is neither its creator nor a deleting command targeting it. Also, setting A(q) false then back to its old value returns exactly the same P(H,A). These follow directly from the Boolean predicate; they say nothing yet about how a changing H acquires a correct O(H), captures deletion targets or admits children.

This model explains several proposed witnesses without claiming more:

- B inserts X between A's a and b. If only A created a/b and A did not delete X, deactivating A leaves X visible. Restoring A returns aXb **only if O(H) already places it there**.
- A and B both delete one original b. Disabling one deletion leaves the other active, so b stays hidden.
- An invisible creator toggle changes A even if P does not change. A receiver needs that fact for later continuations; text equality cannot replace it.

These are consequences of the proposed projection. They do not prove that the proposal is the right undo semantics, that a wire protocol reconstructs it, or that an efficient implementation refines it.

### an invisible-undo calculation

Let command C create `a`; peer command Q create `B`; C's admitted child delete that B and insert `x`. Keep the original element identities and assume the agreed order puts a before x.

| A(C) | A(Q) | visible text under this candidate |
| --- | --- | --- |
| true | true | ax |
| true | false | ax |
| false | false | empty |
| false | true | B |

The first two states have equal text but differ on the next undo of C. A wire/snapshot that identifies them cannot implement this candidate's continuation. Reactivating Q after both are inactive reveals B; reactivating C hides B and restores ax. This calculation motivates an explicit activity event and redo item. It does not implement either, or decide general restoration placement.

## 4. why that is still short of local sequence undo

**Ordering:** the model assumed O(H). A real algorithm must integrate insertions into historical gaps when parents are inactive, maintain the stated affinity and avoid erasing ordering evidence. Before-a and after-a histories can have the same visible Xb. The earlier requirement was Xab and aXb after restoration; Ren decided on 2026-11-02 that both give Xab in this scenario ("I kind of want a to stick with b"). That decision covers this scenario only: the general placement rule for longer runs and concurrent insertions is still open. Retaining both histories' gaps remains necessary evidence for whatever rule is chosen; a visible-index inverse or equal spelling cannot tell the histories apart.

**New work after undo:** H is not fixed when a peer inserts while another contribution is inactive. We need a complete integration law that preserves the author's observed placement and converges with a peer that received the activity later. “Filter active operations then replay” may leave missing causal references and is not an algorithm. The conditional fixed-H argument cannot be extended to this case by assertion.

**Grouping and late children:** a command can acquire noncontiguous contributions after other commands/imports. We need membership admission and rejection laws, distinct primary-continuation/child tokens, and a policy for completion while inactive. These are not supplied by a per-element visibility equation. The current proposal rejects a late child while its trigger is inactive; whether that is adequate for both consumers requires review.

**Selection and redo:** one pop must consume exactly the selected item even when invisible; no hidden scan to an older visible item. New primary work, explicit continuation, child work and imports have different stack effects. A correctly replicated activity map does not prove these local transitions or crash-resume continuation.

**Admitted histories:** identity/authority checks, causal completeness, duplicate/conflict handling and snapshots must recover every fact used by the interpretation. For legitimate unique writers, different causal deliveries should agree. Under equivocation, rejection after different prefixes does not by itself guarantee agreement between peers.

**Costs:** retaining all history avoids one GC problem but provides no useful asymptotic or phone bound. Cold reconstruction, target sets, group membership, anchor resolution and receipts need cost measurements against both consumer profiles.

## 5. what I recommend next, and what I am not claiming

The contribution-deactivation model remains a candidate because it expresses our independent-peer and invisible-activity examples clearly. I have not shown it implements the local undo behavior Ren wants. Nor have I shown that the register restoration algorithm generalizes to sequences with those same examples. We should not choose either by terminology.

The [stable questionnaire catalogue](observation-catalogue.md) now names the observation families and their open decisions. A response becomes a candidate expected outcome only after reviewing its assumptions, interactions and consistency with the other scenarios. It does not become an acceptance assertion by majority vote.

The next research artifact should fix the intended observations for local sequence undo, including overwrite/replacement and edit-after-undo cases; give a complete order/target/activity interpretation; and derive a finite-history implementation with an implementation-linked proof plan. Any conflict between the desired observations and a literature policy must be resolved explicitly. No user study or paper citation here establishes a uniquely correct user expectation.

The [API/verification document](api-verification.md) identifies the exact unfulfilled obligations. Approval of the overview should not count as approving an undo algorithm or verified-undo claim. Dark/Loro remain parked, and no new engine implementation is authorized merely by this analysis.
