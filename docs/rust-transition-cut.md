# the first Rust boundary: author and admit the same edit

**Proposed implementation/proof cut, not implementation authorization.** This
reconciles the merged references with milestone 2 of the [roadmap](../ROADMAP.md).
No Rust document transition exists yet; `src/lib.rs` is still a scaffold. The
Boolean-loop proof does not discharge any obligation below.

The first boundary to cross is a local atomic replacement becoming one immutable
fact, then being admitted by a second Rust instance. The insertion must get the
same identities, scalar payloads and positions on both. Its deletion must not
publish if placement or a resource check fails. Extending that boundary to
Undo/Redo and explicit Restore is required for the milestone, not another
optional research project after declaring an edit-only crate delivered.

## 1. what the existing code can supply

These sources have different jobs; concatenating their receipts is not a
refinement theorem.

| source | reuse as the reference for | missing at the Rust boundary |
| --- | --- | --- |
| `hybrid-restoration/model.py`: `Event`, `Doc.put`, `visible` | deletion atoms, releases, creator withdrawals, reactivation and token cancellation | typed Rust facts, extracted admission/effect interpretation and their laws |
| `hybrid-restoration/sessions.py`: `edit`, `undo`, `redo`, `inspect_restore`, `confirm_restore` | own-action selection, private continuation, frozen masks and issued-selection binding | jointly transactional session/document/placement state; adopted first-cut choices |
| `ordered-gap-reference/order.mjs`: `interpret`, `between` | mathematical expanded-key interpretation on the author's causal insertion basis | machine proof of the written construction and representable-integer conditions |
| `ordered-gap-reference/tree.mjs`: `treeInterpret`, `expandTree` | proposed prefix-sharing representation and diagnostic key expansion | Rust tree-to-key simulation; incremental operations are not supplied by this replay interpreter |
| `combined-admission/admission.py`: `Combined.put` | reconstruct author basis, validate birth/scalar linkage, jointly publish effects/placement/exact packet | actual Rust authoring plus admission; no Python/Node subprocess in the shipped transition |
| `pending-recovery/inbox.py`: `offer`, `drain` | evidence for distinguishing resource deferral, invalidity and caller-owned overflow | not a dependency on adopting its inbox or checkpoint format for milestone 2 |

The references currently use three trusted writer tags; the proposed Rust cut
has two externally fenced writers. Restrict the writer domain explicitly when
comparing them. A third receiving test replica can observe those two writers;
it need not acquire a third author identity. Tags are consistency inputs, not
authentication. No local type can prove the caller prevented a split writer.

The bridge explicitly constructs `Session(..., skip_policy='retain')`. New
Session construction now also defaults to the approved retain behavior; explicit
consume and prior evidence remain historical comparisons. Saved sessions retain
their recorded policy. A Rust test must name the selected profile rather than
infer product semantics from whichever comparison interpreter it imports.

## 2. one owner for the commit

A local call needs a **trial of the whole instance**, not a session event followed
by a fallible placement call. In the current Python reference, `Session._publish`
updates the effect document/counter, and the ordering bridge records placement
separately. `Combined.put` instead commits a trial tuple, but owns no private
session. Neither alone supplies this local atomic boundary.

The proposed Rust instance owns:

- accepted exact structured facts, including each birth event's original gap;
- effect state and the insertion representation derived from those facts;
- one local writer's next counter, own items, undone membership, redo entries,
  selection stamps and current Restore tokens;
- the local inspection/confirmation capability state, if exposed by this slice;
- the chosen profile limits and the local basis/version used by proposals.

Do not copy every Python field merely because it exists. For example,
`ignored_victims` is retained reference history, not justification to restore an
implicit victim-selection path. The representation must explain each field's
future observation before adding it. There is no byte codec, persisted session,
transport outbox, worker or wall-clock state in this milestone's cut.

The local-call sequence is:

1. Validate the call and its basis/selection. Read one immutable before-state.
2. Select identities and author a trial fact using the local writer/counter.
   Freeze its causal prerequisites and any restoration masks **now**.
3. Apply the same fact admission rules used for a received fact; compute its
   author's visible gap from its causal closure, not from extra receiver facts.
4. Check placement, representability and the selected capacity limits. Compute
   the proposed private-history continuation against that same trial result.
5. Publish the entire next instance and return the authored fact together.
   No emitted update, counter advance or stack change precedes this commit.

A failed or blocked call must not leak a fact through a returned publication
channel. An empty call must not mint a new ID. A successful invisible Undo is a
different result from an empty Undo and may advance history and mint a fact.
An exact remote duplicate changes neither the document nor local history in
this direct-admission cut. PR12's `offer` can drain *other* pending entries after
a duplicate; that larger inbox behavior must not be imported under this promise.

For a received structured fact, the owner is the caller until admission succeeds.
A missing prerequisite or resource limit returns a deferred disposition with no
accepted-state publication; the caller retains the exact original fact. Conflicts
and structurally/semantically invalid facts reject unchanged. Do not use an
unqualified error result to tell a caller it may discard a deferred edit.
Milestone 2 need not ship an internal inbox to make that ownership explicit.

The raw admitted fact language and local command language differ. `Doc.put`
checks token/birth author consistency, not that a remote release was selected by
some private Undo stack. A theorem about local command authorship must not be
advertised as a remote admission guarantee or as authentication.

## 3. the abstraction the extracted code must meet

Let `abs(S) = (F, H, C, P)` for the specified slice:

- `F`: the accepted map of exact structured facts, modulo map storage order;
- `H`: this local session's selected private continuation, including counter;
- `C`: profile limits and writer assignment;
- `P`: live inspection capabilities and the bases/selected sources they bind.

The semantic reference derives deletion/withdrawal visibility from `F` using
`Doc`; it derives insertion bases/visibility from each birth fact's causal past
using the combined-admission rule. The candidate expanded-key interpreter gives
the whole historical order; filtering that order by current visible identities
gives the scalar sequence. Rust's proposed tree is an implementation of that
interpretation, not an additional caller-supplied order or a second visibility
policy. Exact duplicates compare the retained fact **including gap**, not just
the current visible effect.

`H` is not replicated. Different writers need not have equal stacks after sync.
Their shared semantic documents must agree for the same complete valid `F`.
Likewise `P` is process/session-local; a replicated operation never carries an
issuance handle. Inspection may create a capability: it is not pure equality of
all instance state. It must preserve `F`, text, history and allocator. Failed
confirmation preserves those and the capability state; successful confirmation
binds the issued source even when another valid source has identical effects.
A double confirmation must fail once the before-basis changes.

The first Rust proof statements must name these state components, not compare
only final strings:

1. **Local refinement:** for every well-formed `S` and supported call `c`, the
   extracted Rust result and `abs(S')` match the selected reference transition,
   including structured errors/empty/blocked/invisible results and the returned
   authored fact. All successful branches preserve well-formedness.
2. **Admission refinement:** for every well-formed `S` and in-domain structured
   fact `f`, admit, duplicate, invalid and deferred branches match the declared
   reference disposition. Admission leaves `H` unchanged: importing facts never
   adds/prunes items, redo or allocator state. It creates no capability in `P`;
   a changed document basis can only make an existing inspection stale. An exact
   duplicate leaves that basis unchanged. Trial publication updates the shared
   derived planes together.
3. **Rejection neutrality:** ordinary rejection, deferral and blocked results
   leave all specified instance components unchanged and return no new fact.
   A successful read/inspection has its separately specified permitted change.
4. **Representation:** expanding Rust tree nodes equals the reference key map;
   visible traversal yields the same ordered `(identity, scalar)` pairs. Fresh
   allocation cannot collide under the external single-writer premise.
5. **Fixed-fact delivery independence:** any legal causal schedules of the same
   valid finite fact set produce the same shared interpretation, provided those
   facts fit the declared domain and are eventually admitted. Derive effect and
   placement independence; neither is an axiom called “the CRDT law.”

The fifth obligation does not cover differing accepted subsets at a capacity
limit. A caller holding a deferred fact has not synchronized that fact. It also
does not identify two presses authored with different knowledge: the frozen
masks can differ. Scope the quantifiers to arbitrary finite valid histories in
the chosen profile, not only the generated test depth.

**Budget-prefix obligation (separate from convergence).** To infer that *every*
causal replay of a fitting final fact set can admit without resource deferral,
prove that every causally closed prefix fits the same profile limits and numeric
representation. A sufficient condition is prefix-monotone aggregate measures
plus state-independent per-fact checks. Events, births and the sum of stored
expanded key digits have that candidate monotonicity because hidden history
remains and an insertion's keys come from its fixed author basis. Packet size,
scalar/dependency counts and counter validity are checks on the original fact;
retry must not rewrite it. This is an obligation to prove for the selected Rust
representation, not a machine-checked property of today's reference.

A limit on current visible size is not prefix-monotone: insertion can exceed it
before a later deletion shrinks the final text. Final-fit alone then proves
neither immediate admissibility of every schedule nor eventual progress. Such a
profile needs a separate prefix-admissibility/deferral argument. This document
does not prohibit all non-monotone release budgets. Conditional agreement after
all fixed facts are admitted (obligation 5) and a claim that every schedule will
get there are different claims; the former does not itself require monotonicity.

These are obligations to discharge against actual extracted Rust functions.
The present Python/Node programs are executable comparison oracles, not foreign
functions trusted to compute the shipped result. Their finite receipts do not
prove the reference laws. The written order argument is over mathematical
integers: Rust overflow/height exhaustion must reject before mutation, or be
excluded by a proved profile bound. No wraparound or unproved “large enough”
integer premise is allowed. Supporting reference theorems remain work too.

## 4. implementation order after adoption

Each row is a connected acceptance slice, not a separate replacement MVP.
Rust transitions and their extracted proofs advance together. A passing helper
or a one-writer demo is not the exit.

| slice | concrete boundary | proof and distinguishing control |
| --- | --- | --- |
| joint local edit / remote admit | two Rust instances author, send and admit insertion, deletion and replacement; exact duplicate and changed-gap conflict; limits fail without partial state | local/admission refinement plus whole-instance rejection; publish trial too early must fail the unchanged theorem/check |
| ordered observation | hidden-gap and concurrent insertions on those facts; scalar payload and identity agreement | tree/key simulation and author-basis independence; receiver-visible gap or receiver basis mutation must fail |
| history continuation | the same two instances run own Undo/Redo and explicit Restore; retain skips, blocked top redo, identity-ineffective cases | selection/effect refinement and unchanged allocator on blocked/rejected calls; consume-skips and blocked-redo-pop controls must fail |
| inspect / confirm | replacement Restore lists what returns and remains; equivalent-effect source substitution rejects; intervening basis expires inspection | issued-selection binding and trial commit; swapping to a second valid source or accepting stale private basis must fail |
| external caller | a separate native consumer uses the crate calls above under delayed/duplicate structured delivery, including caller-retained deferrals | no model-internal access; source-linked obligations plus directed cases and a declared bounded history/schedule generator |

The first two rows share an acceptance boundary: local/admission refinement
depends on the ordering representation lemmas. They must develop together; the
first row cannot be called verified while assuming the second. The eventual
crate must exercise all rows before the milestone-2 exit. A readme
must enumerate missing general anchors, grouping/children, persistence, portable
encoding, receipts and bindings. One call is one primary item; it is not a
silently simplified implementation of the eventual grouping/child contract.
The generator must compare private continuation and returned results as well as
ordered IDs/scalars, preserve failures, and distinguish author-time knowledge
changes from rescheduling a fixed fact set. No general theorem follows merely
from increasing its depth.

## 5. decisions and remaining work before code starts

No new product answer is inferred from this document. Reuse the
[four decision scenarios](first-cut-decisions.md), rather than making Ren read
this machinery to answer them.

| dependency | what is still required |
| --- | --- |
| retain | approved and now default in the reference/oracles, with consume evidence preserved; carry it into the Rust selection proof |
| frozen observed masks | approved for the first cut after conditional yes and completed peer confirmation; preserve the original masks and later deletion behavior |
| new-work redo | adopt explicit keep/clear continuation or select a narrower alternative; no silent default |
| exact returning IDs | adopt the observable contract before claiming old handles target returned occurrences |
| candidate ordering | review/adopt the cut's longer-run/replacement domain and explain per-event-only cohesion; `a2413b` remains a limitation, not a broader typing-run promise |
| budgets | choose supported workloads/limit response; current 128 events/512 births/etc. are experiment ceilings, not release targets; measure candidate costs before proposing numeric release bounds; prove prefix-admissibility before inferring it from final-fit |
| Latte regeneration | Ren directed the compiler to stay private; continue private authoring/public F* checking, and validate locked emitter access before proof slices without assuming anonymous regeneration |
| reference proof | connect effect/admission invariants with the finite-history ordering argument, and formalize the needed laws without assuming them |
| implementation start | approve the concrete slice/profile after the semantic, abstraction and error contracts are reviewed |

The tooling row is an existing dependency made explicit, not a new claim that
Latte must be published before work can proceed. PROVENANCE.md records the
private emitter revision used for the scaffold. Ren directed Latte to remain private in Discord message 1567303368131608637.
The selected tooling arrangement is to use that locked authoring route, publish the authored Latte and generated F*
with provenance/drift checks, and let public checks verify the committed F*.
Anonymous users still cannot regenerate emission. Regeneration availability on
Lynn's machine is not inferred from old receipts: check it when a proof slice
starts and report a concrete blocker if unavailable. Publishing or vendoring
the unlicensed compiler is outside this cut and contrary to the current direction; silently replacing
Latte or relaxing a failed theorem is not an alternative.

PR12 closes a useful reference retention question, not the last line of this
table. Its checkpoint, canonical JSON byte count, Python allocator behavior and
Node timeout are not Rust ABI requirements. Versioning and durable recovery
belong to the later explicit boundary, not a hidden dependency of this cut.

This document adds no new reference interpreter, Rust implementation or CRDT
proof. All V1–V9 remain unfulfilled. It specifies which parts of V1–V6 the
milestone must actually discharge for its subset; general anchors/grouping,
V7 receipts, V8 codecs/recovery and V9 bindings remain outside this early cut.
The trusted toolchain and public/private regeneration limits stay those in
[proofs/README.md](../proofs/README.md) and [PROVENANCE.md](../PROVENANCE.md).
