# native keyed registers before the complete text profile

**Status: scope approved, implementation not delivered.** The first subset
supports writing, reading and replicating keyed register values through the
actual shared causal layer. It excludes Undo/Redo. Ren approved a single-write
checkpoint followed by atomic multi-write register events, including Carbon's
multi-field creation, before keyed collections.
This does not close the full [register contract](register-contract.md) or remove
its history requirements. The reference experiments are not the native implementation.

## what the caller must be able to do

A separately compiled native caller creates two real replicas, writes independently
keyed values, exchanges the resulting events and reads their values. It exercises
concurrent writes, a later causal overwrite, an equal-to-observed no-edit,
duplicate/conflicting events and invalid/capacity rejection. It can compose these
operations within the supported bounds, rather than call a hardcoded replay.

Keys are caller data and are independent of writer IDs. Values can retain tagged
opaque bytes. Carbon owns format interpretation and incompatible-editor locks;
an unknown application format inside a known register write is not an unknown
engine operation. No plugin ownership is encoded into the CRDT's identities.

For writes/reads, carry the applicable register contract:
- decide whether a write counts against its captured author basis; a write equal
  to its observed value is no edit;
- select the visible value using causal maxima and the prescribed Lamport/writer
  ordering, with the same document initial values on compared replicas;
- retain every counted write, including concurrent losers. A deterministic winner
  is not permission for winner-only storage/compaction or a new GC scheme;
- validate and compute privately, then publish once. Specify duplicate, conflict,
  invalid and capacity returns and preserve the promised state/counter neutrality.

Initial-value configuration, concrete writer representation/fencing assumptions,
encoding of the retained value and numeric supported limits must be explicit at
construction. The shared arbitrary-ID boundary does not require changing the
text Alice/Bo representation at the same time. An example's u64 IDs do not supply
a public allocation/recovery protocol or prove random identifiers unique.

## proof work belongs to this client

Give the register a meaning independent of the native interpreter, over its
retained valid closed history and agreed initial configuration. Link the actual
Rust write/read/receive transitions to that meaning, with all-return refinement,
exact event/payload publication, and private-counter/rejection obligations. Prove
that the supplied equality/clone policy is exact on the complete payload.
Comparison-relative classifier laws alone do not establish duplicate correctness.

Use the shared graph/shell implementation rather than copying it. Generalize
or instantiate the graph laws needed by these actual calls, and retire proof-only
forwards along those boundaries while preserving the old concrete text claims,
domains and intended controls. A wholesale wrapper-retirement sprint is not an
extra prerequisite. The existing batch example does not discharge this client's
semantics or refinement by resemblance.

The acceptance slice includes fresh pinned Rust extraction, full Latte/view
parity, wrong-body and wrong-actual-argument controls, callee-contract dependence
with owning bodies withheld, scoped review alongside CI, and complete exact-head
acceptance. Neither a finite reference match nor a passing generic helper alone
closes the delivery.

## convergence shared with text: goal and conditions

The intended common result is about actual admitted history, not just equal
rendered values. For replicas with the same valid closed event set and initial
configuration, shared storage/canonicalization laws should give the same exact
canonical history. Each client must then prove that its native transition/state
realizes the specified interpretation of that history. Different physical layouts
may need their own refinement bridge.

Factor the actual shared proof work where possible: exact retained events,
whole-payload duplicate/conflict policy, causal basis, delivery-independent
canonicalization and transactional publication. A theorem saying an arbitrary
function gives equal results on equal inputs is not evidence that either native
client implements it. Any generic claim must state its actual order, equality,
closure and client premises, then discharge them at real construction/call sites.

For text, independent placement/Tree.add meaning, author-basis interpretation,
intermediate fitting and the all-return bridge remain obligations. Selected IDs
or a shared event order alone do not establish equal placements or text
convergence. Preserve current universal text statements while adding the missing
semantic claims; no weakening to obtain a shared label.

Strong eventual consistency additionally needs eventual delivery/admission and
termination/progress in a declared domain. Transport is external to the crate;
missing dependencies, finite capacity and retry conditions must be explicit.
Equal limits do not guarantee equal admitted subsets under different deliveries.
Do not turn equal-history convergence into an unconditional liveness claim or
compare device-local private stacks/counters as replicated document meaning.
No whole-CRDT strong eventual consistency theorem is delivered by this plan.

## return point and remaining scope

At basic register-slice acceptance, revisit the shared convergence result against
the actual text engine, then implement and accept one agreed semantic/refinement
slice before starting another CRDT kind's implementation. This is a concrete return point,
not a requirement to finish every text feature before collections. Collection
contracts can progress alongside it. Text meaning/progress/admission, anchors and
history retain their eventual acceptance requirements.

Register Undo/Redo remains a distinct follow-up with the answered q13–q17/f1–f7
histories intact. Blocked-Redo consumption and new-work redo choices are not
silently adopted. Partial write prefixes are not acceptance of those histories.
Collection K1/K2 answers stay fixed; mutable-field Restore, locked-record removal,
key shape and coupling require their own contracts. Atomic multi-write register
events need explicit within-batch observation/counting semantics and whole-batch
rejection/publication. They do not decide the open multi-text BirthId question. Runs, incrementality, codecs, persistence, arbitrary
writer allocation and Carbon integration remain separate work.
