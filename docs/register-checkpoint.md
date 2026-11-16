# native single-write register checkpoint

**The [single-write safety checkpoint](https://github.com/carbon-study/nickel-crdt/issues/105#issuecomment-6905714405) is accepted** on main
`58b7e61`, with the exact reviewed `591c23a` source tree and complete green
[main workflow](https://github.com/carbon-study/nickel-crdt/actions/runs/43773921327).
The later sharding merge changes no native/proof/pin bytes. This is not a stable
verified release, universal admission/progress or SEC. Atomic multi-write
registers follow as a separate delivery after the approved shared exact-past
consolidation, then the agreed implemented text semantic/refinement slice before
collections. No Undo/Redo is implemented.

## accepted composition and its domain

`RegisterPublic.public_history` combines the retained-history invariant and
positional ID uniqueness. The actual constructor establishes it; every
`receive` and `write` return preserves it. Under that invariant and the same
initial configuration, `public_read_is_the_causal_read` connects the actual
public read to the independent causal-maxima meaning.

`receive_added_meaning` and `write_counted_meaning` bind successful publication
to a fresh valid whole fact and the exact retained-history extension, including
losing writes. `RegisterFrontier.counted_write_basis_is_whole_history` identifies
the successful local write's actual validation basis with the literal complete
pre-write fact slice. `receive_duplicate_meaning` and `write_noedit_meaning`
connect those outcomes to retained whole facts and the causal read. Public
producer contracts compose all-return history preservation with exact private
counter/identity, publication and neutrality laws. The equality/clone callbacks
are checked on the complete fact payload.

These safety and successful-result laws do not prove every valid offer is Added,
every requested write succeeds, termination, or an independent iff classification
of every error code. Complete full-register history/Undo, delivery/progress,
recovery and convergence remain outside this checkpoint. Caller fencing and the
translation/model/compiler/runtime trust boundaries below still apply.

The component accounts below preserve each earlier theorem's individual scope.
Where one component alone does not establish ancestry, retention or validity,
that limitation does not remove the separate accepted composition above.

## manipulate a register

`register::Replica::new(writer, initial)` creates an empty history.
`write(key, bytes)` returns a new structured fact, or `None` for an equal-to-observed
no-edit. Relay a fact with `receive`, then use `read(key)`. The separately compiled
caller exercises two actual native instances:

```sh
cargo run --locked --example register-checkpoint
cargo test --locked --test register_checkpoint
node scripts/check-register-native.mjs
```

Keys and writer IDs are independent u64 values. The caller supplies globally
unique, fenced writer streams: no concurrent producer, rollback or ID reuse.
Counters start at 1; receiving the producer's old history is **not** restoration
of its private counter. There is no checkpoint/recovery protocol.

Values are opaque byte strings. Their application encoding must carry any format
family/version identity Carbon needs; Nickel neither interprets nor validates that
application tag. The same explicit initial byte string applies to every key.
Compared replicas of a document must agree on this configuration. No plugin
ownership is encoded into keys or writer identities.

There is no engine event-count, parent-count or value-byte policy ceiling.
Optional workload budgets belong to callers; see [the migration](policy-budgets.md).
No register-budget harness is delivered by this candidate. The retained capacity
tests use a text-only caller guard, not register engine Capacity outcomes.
No automatic GC, winner-only compaction or buffering policy is selected.

Each counted write deep-clones the current replica; its successful receive stages
another replica clone and canonicalizes all retained facts. Facts retain both the
new value and the observed value, as well as their parent IDs. Copy work per
counted write therefore grows with retained history. For N accumulating counted
writes whose value and observed byte strings are bounded by S bytes, the
cumulative payload-byte copying component is O(N² · S), in addition to parent-ID
copying and canonicalization work. This is a source-level cost description, not
a measured runtime bound or a new workload ceiling. Equal-value no-edit returns
before constructing these candidates.

## retained meaning and admission

A fact carries its ID, direct causal parents, key, new value, frozen observed
value and Lamport clock. Only counted writes become facts. The observed value is
checked against the exact transitive author basis, never the receiver's unrelated
concurrent state. Its Lamport clock is 1 plus the maximum over *all* facts in that
basis, including other keys. Receiving does not advance the private author counter.

Read chooses the highest (Lamport, writer) at that key, or the initial value if
none exists. The intended causal-maxima meaning agrees with this scan when valid
clocks strictly increase along ancestry; the accepted public-history composition
preserves that invariant through the actual constructor and returns. Equal priority values cannot be
assumed unique on arbitrary malformed arrays. All counted losing writes remain
stored. Storage canonicalization is writer-first and is not read priority.

Whole-fact duplicate classification comes first, before payload validation.
Same ID with different parents or payload is a conflict. For a new identity:
counter 0 is invalid; shared graph admission checks repeated/missing
dependencies and producer ancestry; the client then checks frozen
observation, a counted change and the exact next clock. Errors and duplicates
publish nothing. A new local write advances its counter only in the detached
successful candidate. Clock/counter exhaustion returns an explicit error.

Missing dependencies require the external caller to retry after delivering them.
The former dependency-cap/frontier refusal has been removed, rather than
replaced by a larger configured cap or a different causal context. Counted writes
still cite the whole current frontier. Counter/clock exhaustion, writer fencing,
validity and termination remain separate obligations. There is no unconditional
eventual delivery/admission or SEC result.
Rust allocation failure, the hax translation and its pinned models remain trust
boundaries; finite tests are not universal validity or progress proofs.

## current evidence boundary

The external test has a separate causal-closure/maxima oracle and checks every
dependency-respecting delivery of one six-event, three-writer history, at every
prefix. Other tests cover retained concurrent losers, independent keys, author
basis contamination, no-edit, exact conflicts, malformed input, numeric limits
and snapshot neutrality. The native runner mutates actual source bodies and the
policy construction site; it requires the named external test to fail after
successful compilation. These are native controls, not F* owner rejections.

The authored Register proof work concerns exact byte comparison, priority
selection/read projection, exact shared-shell publication and equal-value no-edit.
The actual public write has an all-return neutrality/identity/counter law: every error and
no-edit preserves the entire replica exactly; a counted success returns the
pre-write producer identity and advances the private counter by exactly one.
This law withholds receive, frontier, clock, read and byte-comparison bodies: it
does not assume the detached planner is correct. The separate `write_installs_successful_candidate` law now binds every counted
success to the exact detached planner candidate for the returned fact. That fact
has the pre-write producer identity, requested key/value, pre-write observed read,
and the exact returned frontier/next-clock results. Candidate facts and
configuration are installed unchanged, with private state framed before the
separately proved counter advancement. Errors/no-edit preserve the whole replica.
Both write laws are all-return safety statements: a write that always returns
an unchanged-state error satisfies them. They do not prove that a fitting, valid
write succeeds; that admission/progress obligation remains open. Native tests
exercise actual successful writes, but do not supply a universal success theorem.
Its caller withholds receive/planned and the frontier/clock/read/byte bodies;
publication and private-frame contracts supply the connection. This still does
not prove which facts the planner/canonicalizer retains or history/clock validity. Receiving now has a separate all-return private-state frame law: added
facts, duplicates and every error preserve the writer, private producer counter,
initial bytes. Its composition checks actual prepare/execute policies
and the shared planning/publication contracts with those bodies withheld. It
does not establish which facts canonicalization retains.
The current theorem name, `write_publication_on_every_return`, does not mean
successful candidate installation follows from that law alone. The new
installation law is separate: the counter-bump-without-installation fault that
satisfied the old counter law is its dedicated actual-source control. These frame/installation laws alone do not supply independent retained-history
meaning; that separate link is supplied by the accepted public composition above.
Native and proof controls cover premature counter publication; additional proof
controls corrupt the successful counter and returned identity.

None of these component statements alone establishes valid-history preservation
or full client refinement; the accepted single-write composition above supplies
its separate safety links. Shared convergence, admission/progress, the multi-write
contract and full register history/Undo are not established by this checkpoint. The existing text theorem statements and implementation are unchanged.

Equal-value no-edit has no engine value-byte-budget premise in this API. The
older bounded no-edit evidence at `52f597a` required value fitness and did not
let equality bypass that policy check; that is a historical claim about the
pre-migration engine, not a condition or guarantee of the ceiling-free API.

### added-receive payload boundary

`validation_is_exact_basis_checks` characterizes the actual validator in both
directions: the actual shared admission and basis-selection calls succeed, the
counter is nonzero, the observed bytes equal the read of
that selected basis, the new bytes differ, and its clock equals the actual
`next_lamport` result on that basis. `planned_checks_payload` and
`receive_added_checks_payload` transport those checks to the actual public
`Added` result through checked planning and publication contracts, with their
bodies withheld. This does not apply to `Duplicate`, which deliberately skips
validation, nor assume the prior replica is reachable or valid.

The basis and clock calls remain explicit boundaries: these laws do not yet
identify the selected basis with independent transitive ancestry. The separate
clock theorem below supplies the mathematical maximum law, which does not follow
from these earlier computational checks alone. They do not
by themselves prove retention through canonicalization, valid-history preservation, fitting
admission/progress, full refinement or SEC. The validator equivalence is stronger
than one-way safety over its computed stages; it still is not a guarantee that
the full receive/write operation succeeds on an independently fitting history.

### mathematical selected-basis clock

`next_lamport_is_maximum_successor` now connects the actual Rust scan to an
independent maximum condition on every typed input slice, without a valid-history
premise. `Ok(clock)` is exactly one above the maximum input clock (zero for an
empty slice). `Err` is exactly `ClockExhausted`, with an input at `u64::MAX`.
Every key participates in the scan. The invariant records both an upper bound
and attainment, so an invented larger clock is excluded.

The scan now uses the existing index-for-loop interface. The previous slice
iterator extracted through the pinned model's unconstrained `iter_fold`; no
model, compiler or checking option was changed to supply a missing law. The new
proof consumes `LoopUtil.plain_preserve_any` and withholds the range-fold body.
The native public signature and arithmetic/overflow behavior are unchanged.

`receive_added_clock_is_maximum_successor` transports that mathematical result
to the actual public `Added` receive through the checked payload law, with receive,
clock calculation, shared admission and basis-selection bodies withheld. Its
basis is still identified by the exact computational admission/selection calls;
identifying that basis with independent ancestry remains open. This is not yet
valid-history preservation, independent full client refinement, fitting-write
progress or SEC, and it does not cover the deliberately unvalidated Duplicate
path.

### exact whole-fact retention through the shared canonicalizer

`Canonical.canonical_preserves_exact_contents` is a payload-, identity- and
error-generic law about the actual shared Rust canonicalizer. On success, the
output has the input length and exactly the same whole fact values. Its explicit
policy premises require logical ID equality, whole-fact copying and logical
whole-fact equality. This law needs no text placement, register clock or reachable
state premise. It does not prove that canonicalization succeeds, that the output
has a particular order, or that two clients interpret equal histories equally.

The proof composes checked choice, copying, append and loop laws, with those
native bodies withheld at their callers. It first establishes that each output
slot selects an original whole fact and has a fresh ID. A finite pigeonhole
argument then rules out a missing original. The checked vector models remain a
trust boundary; the native helper bodies are not replaced by authored algorithms.

The register discharges the actual constructed policy's value premises.
`prepare_appends_exact_fact` and `execute_preserves_exact_fact_contents` connect
that generic result to the actual planning stages. The actual public
`receive_added_retains_exact_facts` and `write_counted_retains_exact_facts` then
state: an Added receive or counted successful write retains every old whole fact,
adds the exact offered/returned fact, introduces no other whole fact, and increases
the retained length by one. These are conditional success laws on every typed
replica, not only reachable replicas. Earlier publication, frame and installation
laws still cover their separate all-return obligations.

The content law alone does not supply ordering, independent ancestry/valid-history
preservation, history agreement, full client refinement or fitting admission/progress. An operation
that always refuses is not excluded by these success-only laws. No SEC or
checkpoint acceptance follows from this cut alone. Rust APIs and implementation
bytes are unchanged; the native extraction roots include the complete shared
layer so the full generic EventGraph module can be checked rather than sliced.

The focused controls cover wrong shared push/selection/output bodies, wrong
register append/canonical-input arguments, and checked loop, policy, planning,
publication and installation dependencies. The original diagnostic omitting the
step's append-contract call failed a nonterminal query and was not credited.
Review traced it to a Latte statement-sequencing defect: an assertion emitted
after an ungrouped match belonged only to its final arm. The postconditions
still checked, but that did not establish the intended all-arm caller isolation.

The bounded repair puts the final query explicitly inside every branch of
`LoopUtil.preserve`, `Canonical.step_preserves_content` and
`Canonical.canonical_preserves_exact_contents`. The step also withholds the
lower push contract so it must consume the append contract. These are tail
matches; their query scope no longer depends on the repaired emitter. The
statements, domains, native code, runtime, models and checking options are
unchanged. New controls cover loop unroll/induction/end, the formerly uncredited
append edge, and the final selection/coverage composition. Existing owners and
controls are retained with exact branch-local boundary counts.

This repairs the three affected match sites in the register dependency closure,
not the ten other inventoried text-side match sites. The private compiler source
fix is merged but is not activated in Nickel. For the bounded three-site repair
at `2de2294`, the complete register closure verified with both the unchanged pinned
producer and the corrected experimental producer. That retained comparison
supersedes the earlier failed `LoopUtil.preserve` run; it does not claim a new
corrected-producer check of every subsequent candidate. The
[retained comparison evidence](https://gist.github.com/lynn-in-residence/690c8d6e8dc2744f87e989afb48e34e2)
includes the two complete-closure logs and source/view identities.
The remaining text audit stays open. The bounded register closure has closed
scoped review and exact-head CI as part of the accepted checkpoint; this does not
activate the compiler repair or extend the corrected-producer comparison.

### strict storage order through actual publication

The generic `Canonical.choose_is_least` law follows the actual shared minimum
scan. `canonical_outputs_strict_id_order` establishes strict ID order for every
successful canonical result, under explicit irreflexive/transitive/total comparator
and exact value-policy premises. The input need not be a reachable history.
The choice and canonical loops use their checked Result-loop contracts; native
membership, step and fold bodies are withheld at the relevant consuming queries.
A scoped boolean-shape lemma supplies the membership result shape under opacity.

The register discharges the actual constructed comparator as writer-first, then
counter. This storage order is separate from the Lamport/writer read priority.
`execute_orders_fact_history`, `planned_orders_fact_history`,
`receive_added_orders_fact_history` and `write_counted_orders_fact_history`
carry the property through actual computation and publication. These are
success-only laws on every typed replica; existing publication/neutrality laws
retain their all-return domains. No new native implementation or API is involved.

The focused gate reverses the actual choice comparison arguments and swaps the
register's actual comparator slot for equality. Fresh extracted native modules
must typecheck before the unchanged semantic owners reject ordinarily. The
policy-slot fault is bound to the complete unique code-masked const declaration;
missing, commented or duplicate policy items refuse preparation. Extraction
explicitly retains `less_id`, already present in the healthy four-module output,
so a wrong policy cannot turn the test into a missing-declaration error.

A separate native-body control changes `less_id` to counter-first, then writer.
That remains a strict total order, but violates the writer-first contract;
`less_id_is_lexicographic` must reject it ordinarily after fresh extraction and
native typechecking. This checks the specified order independently of the
comparator-slot fault and generic strictness premises.

Separate removal controls check minimum-to-step, canonical-to-execute and both
plan-to-publication callers with the relevant bodies and automatic contracts
withheld. The successful execute branch checks strict ordering under opacity
before calling the policy refinement lemma, so its premise cannot be recovered
by unfolding the canonicalizer outside the consuming query.
The native definition visibility added for this cut is exactly the register's
`identity` and `less_id`. New match-consuming queries are branch-local; no compiler
sequencing repair is activated.

The counted-write ordering query also withholds the hinted
`planned_checks_payload`, `planned_preserves_private` and
`planned_adds_exact_fact` contracts. It consumes the checked plan-order and
candidate-installation laws directly; payload, private-frame and whole-history
retention instantiations are not needed at this boundary. Those separate
theorems and their callers are unchanged. Only the last name is new to the
Register fence. The plan-order removal keeps its original semantic owner,
actual call and query boundary.

This ordering cut alone does not establish independent exact ancestry or
valid-history/client refinement; those single-write safety links are supplied by
the accepted composition above. Fitting admission/progress remains open beyond
this checkpoint. Canonical success on unique-ID inputs is addressed separately
below. No SEC result follows from this cut.

### successful canonical agreement on equal whole-fact contents

`Canonical.canonical_is_permutation_independent` composes the checked content
and strict-order contracts: with the same explicit strict comparator and exact
value policy, two inputs of equal length containing exactly the same whole facts
produce identical whole-fact vectors **if both actual canonicalizations succeed**.
Neither input is restricted to reachable histories. The law says nothing about
which calls succeed or about equality of errors.

The finite argument is positional, with no numeric rank or finite identity
universe assumption. Two ordered vectors with the same facts agree one position
at a time: a first mismatch would place the two facts before each other, contrary
to the strict comparator. Equal prefixes and irreflexivity also rule out finding
either fact at an earlier position. Sequence extensionality gives vector equality.
The actual canonicalizer is withheld at the consuming agreement queries; its
checked exact-content and strict-order contracts supply the two results.

`Register.execute_agrees_on_same_fact_contents` discharges the real register
policy and carries this to the actual `execute` calls: equal whole-fact input
contents and lengths, plus two successful executions, imply identical retained
fact vectors. Private writer/counter/configuration fields need not agree and are
not asserted equal. This is not equality of reads across different initial values,
a receive/admission result, history validity or replica convergence.

Four owning removal controls separately withhold the generic ordered-output,
exact-content and vector-equality steps, then the generic agreement contract at
the register caller. The existing fresh-extraction minimum-scan fault remains
the native implementation-sensitivity control for the underlying ordering chain;
it is not relabelled as a direct fault of the new agreement theorem. No Rust,
model, compiler, runtime, budget or source-fence changes are involved.

### canonical success for unique-ID input

`Canonical.canonical_succeeds_for_unique_ids` proves that the actual shared
canonicalizer returns `Ok` for every typed input slice with distinct projected
IDs, under the explicit exact ID-equality/copy/whole-fact equality policy.
This is a success law, not merely a property conditional on success. It includes
empty inputs and does not restrict inputs to reachable histories.

Success does not require a strict comparator: even an arbitrary total boolean
comparison callback keeps the selected index in range. The choice scan cannot
take its error branch, and `None` means all input IDs are already represented.
If the output is shorter than a unique-ID input, a positional pigeonhole argument
rules that out. A step therefore has a selected in-range fact and room to append
before the real `usize` maximum. The checked Result-loop interface carries this
through the actual complete range, preserving the whole-fact prefix invariant
and disallowing an error exit. Strict order is still required by the separate
ordering/agreement laws; success alone does not imply sorted output.

`Register.execute_succeeds_for_unique_ids` discharges the actual register policy
and proves that `execute` returns a candidate for any typed replica with distinct
stored IDs. Its policy precondition is established with the native policy,
constructors and ID projection withheld before invoking generic success. It
does not prove that an arbitrary offered event passes admission, that public
writes progress, or that a replica satisfies independent history validity.

Two fresh Rust fault controls make the actual choice scan and register executor
return errors. Earlier success-only properties can remain true; the new
`choose_finishes_scan` and `execute_succeeds_for_unique_ids` owners must reject
ordinarily after native typechecking. Separate contract removals cover scan
coverage/totality, the finite unseen-ID argument, membership, step success, the
Result-loop rule, the real ID policy and the register's canonical-success call.
The old theorem domains, fences, native implementation, models and budgets are
unchanged.

These laws concern the actual extracted functions under the pinned Hax/vector
models and total logical callbacks. They do not certify allocation availability,
panic freedom or termination of arbitrary external Rust callbacks. The bounded
public runtime caller exercises real successful calls under several comparison
policies; those finite observations do not remove these trust boundaries or
establish admission, valid-history preservation, convergence or SEC.

### positional uniqueness across public returns

the retained vector now has a separate positional-ID property:
`Register.fact_ids_unique` says equal IDs at two in-range positions force the
positions to be equal. this excludes even two identical copies of one fact.
it is stronger than a set-level “same ID means same whole fact” condition.

`facts_order_implies_unique` derives it from the already checked strict
writer-first storage order. `receive_added_has_unique_ids` and
`write_counted_has_unique_ids` apply that implication to the actual public
success results; neither assumes a valid input history for that success-only
claim. `new_has_unique_ids` checks the actual constructor's empty vector.

`receive_preserves_unique_ids` and `write_preserves_unique_ids` preserve the
property on **every return** when it holds before. Added/counted outcomes use
the checked ordering chain; duplicate, error and no-edit paths use the existing
publication/neutrality contracts. the consuming queries hide the relevant
native public/planning bodies and match `fact_ids_unique` as an opaque
predicate at those all-return queries. its definition is established by the
order-to-uniqueness law, not reconstructed from native code at the caller.
this adds exactly that one local predicate to the Register fence. no reachable-state restriction is substituted
for the typed-state statements.

`receive_result_can_execute` and `write_result_can_execute` then discharge
#116's positional uniqueness premise on the actual returned replica and invoke
its checked canonical-execution success law. this says a subsequent pure
`execute` has an Ok result, including after a refused or no-edit operation.
it does not say a refused fact will become admissible, restore a producer
counter, prove a deterministic causal read, or close full client refinement,
valid history, convergence or SEC. all existing hax/vector-model and total
logical callback trust boundaries remain.
