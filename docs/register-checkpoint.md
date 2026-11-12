# native single-write register checkpoint — candidate

This branch contains a runnable candidate, not an accepted verified delivery.
The [approved cut](register-first-cut.md) still requires full client refinement,
clock/valid-history preservation, focused proof controls, review and exact-head CI.
Atomic multi-write registers follow this checkpoint, then the agreed implemented
text semantic/refinement slice, before collections. No Undo/Redo is implemented.

## manipulate a register

`register::Replica::new(writer, initial, limits)` creates an empty history.
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
Counters start at1; receiving the producer's old history is **not** restoration
of its private counter. There is no checkpoint/recovery protocol.

Values are opaque byte strings. Their application encoding must carry any format
family/version identity Carbon needs; Nickel neither interprets nor validates that
application tag. The same explicit initial byte string applies to every key.
Compared replicas of a document must agree on this configuration. No plugin
ownership is encoded into keys or writer identities.

Limits are explicit constructor arguments: retained event count, dependencies
per event and bytes per value. Initial values must fit. Both the new and observed
values of received writes must fit. No automatic GC, winner-only compaction,
capacity increase or buffering policy is selected.

## retained meaning and admission

A fact carries its ID, direct causal parents, key, new value, frozen observed
value and Lamport clock. Only counted writes become facts. The observed value is
checked against the exact transitive author basis, never the receiver's unrelated
concurrent state. Its Lamport clock is 1 plus the maximum over *all* facts in that
basis, including other keys. Receiving does not advance the private author counter.

Read chooses the highest (Lamport, writer) at that key, or the initial value if
none exists. The intended causal-maxima meaning agrees with this scan when valid
clocks strictly increase along ancestry; preserving that invariant through actual
admission is an outstanding proof obligation. Equal priority values cannot be
assumed unique on arbitrary malformed arrays. All counted losing writes remain
stored. Storage canonicalization is writer-first and is not read priority.

Whole-fact duplicate classification comes first, before capacity and validation.
Same ID with different parents or payload is a conflict. For a new identity:
counter 0 is invalid; shared graph admission checks limits, repeated/missing
dependencies and producer ancestry; the client then checks value bounds, frozen
observation, a counted change and the exact next clock. Errors and duplicates
publish nothing. A new local write advances its counter only in the detached
successful candidate. Clock/counter exhaustion returns an explicit error.

Missing dependencies require the external caller to retry after delivering them.
Finite capacities can make receivers admit different subsets under different
offers. There is no unconditional eventual delivery/admission or SEC result.
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
initial bytes and limits. Its composition checks actual prepare/execute policies
and the shared planning/publication contracts with those bodies withheld. It
does not establish which facts canonicalization retains.
The current theorem name, `write_publication_on_every_return`, does not mean
successful candidate installation follows from that law alone. The new
installation law is separate: the counter-bump-without-installation fault that
satisfied the old counter law is its dedicated actual-source control. A full
independent retained-history meaning law remains required.
Native and proof controls cover premature counter publication; additional proof
controls corrupt the successful counter and returned identity.

Its checked statements and remaining control/integration frontier are tracked
with the candidate; none of these alone establishes full register refinement,
valid-history preservation, shared canonical convergence or the multi-write
contract. The existing text theorem statements and implementation are unchanged.

### added-receive payload boundary

`validation_is_exact_basis_checks` characterizes the actual validator in both
directions: the actual shared admission and basis-selection calls succeed, the
counter is nonzero and byte bounds hold, the observed bytes equal the read of
that selected basis, the new bytes differ, and its clock equals the actual
`next_lamport` result on that basis. `planned_checks_payload` and
`receive_added_checks_payload` transport those checks to the actual public
`Added` result through checked planning and publication contracts, with their
bodies withheld. This does not apply to `Duplicate`, which deliberately skips
validation, nor assume the prior replica is reachable or valid.

The basis and clock calls remain explicit boundaries: these laws do not yet
identify the selected basis with independent transitive ancestry or establish
that the clock computation is the mathematical maximum plus one. They do not
prove retention through canonicalization, valid-history preservation, fitting
admission/progress, full refinement or SEC. The validator equivalence is stronger
than one-way safety over its computed stages; it still is not a guarantee that
the full receive/write operation succeeds on an independently fitting history.
