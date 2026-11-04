# Admit a placement and its effects together

A received insertion should not get one identity in the text order and another
in the Undo model. Nor should a failed resource check leave its deletion active
without the insertion. This restricted reference puts an effect event and its
optional insertion gap in one packet, checks them on a trial state, and publishes
both planes with one state-pointer replacement.

```sh
# from the repository root; only this experiment's checks run
nix develop --command bash experiments/combined-admission/check.sh
```

The runner generates actual Session histories from the preceding bridge, then
checks admission, rendering, duplicates and cold/reversed causal replay against
`receipt.json`. Python comes from the existing hybrid reference's locked shell;
Node from the root shell. A persistent JSON-line subprocess uses the unchanged
candidate order interpreter. No service, compiler, browser or full proof matrix
runs. `--record` explicitly regenerates the receipt.

## Packet and state

The input is a **parsed reference value**, `{event: <all Event fields>, gap: n}`.
It is not a public byte format. `gap` is an integer for a birth event, otherwise
null. There are no caller-supplied order IDs, bases or visibility sets.

The effect event carries its causal prerequisites. Admission reconstructs their
ancestor closure and runs the actual effect interpreter on that author basis.
It derives the visible birth set and known insertion events from those facts,
then supplies them to the existing candidate order. It never uses the receiver's
extra concurrent facts to choose the author's gap. A compound replacement uses
the author's pre-edit visible gap; its own deletion does not erase that basis.

This profile requires:

- one of the three fixed **trusted** writer tags, matching `writer:counter` IDs;
- positive safe counters, with the preceding same-writer event in the causal
  past and no later same-writer event there;
- exactly the Session-minted `[writer,counter,index]` birth IDs, each paired with
  exactly one scalar payload in birth order;
- deletion targets visible in the author's causal basis, not unknown/future
  births or births hidden only by extra receiver facts;
- the original Doc admission rules for withdrawal, cancellation, release and
  reactivation. These are raw-effect rules, not proof that every admitted event
  could be selected by Session's private Undo stack.

An exact packet duplicate is idempotent. Changing a duplicate's gap is a conflict,
including when both gaps are valid. This does not authenticate the *first*
packet: a different valid first gap is a different edit. Missing prerequisites
reject without publication; there is no pending-queue implementation.

The stored state is `(Doc, insertion records, exact packets)`. All checks,
including the external order call and the final expanded-key budget, precede its
one replacement. A rejected packet changes neither plane, the duplicate map nor
any allocator (there is no receiver allocator). The scope is a single-threaded
reference call, not concurrent host memory or durable storage transactions.

## Explicit experiment ceilings

`Limits` is supplied configuration: events128, births512, packet8192 canonical
escaped-JSON bytes, scalars per edit64, prerequisite references64, and expanded
key digits4096. These are small **test parameters**, not proposed release budgets
or Ren's adoption of them. Directed tests lower each limit to force rejection.
An order-oracle failure rejects too; its response wait has a five-second deadline.

The packet is already parsed before the size check. Key expansion happens before
its digit-limit check. These checks bound *accepted state* in this finite profile;
they are not streaming decoder limits, CPU/memory isolation, a useful-scale
benchmark or whole-engine resource analysis. Full bases, snapshots and replay
remain expensive. An externally killed Python process is outside this in-memory
transaction model.

A resource rejection does not mean the edit was semantically invalid. The caller
must retain it or report a resource-pending condition, not silently discard it.
If a union exceeds capacity, different arrival orders can retain different
accepted subsets. This experiment does not make that a converged document or
supply recovery, backpressure, negotiated profiles or garbage collection.

## Checked boundary

All46 views from eight actual Session histories are admitted and rendered under
two causal replay orders, with exact duplicate and cold-state comparisons. This
includes concurrent deletions that a receiver already knows about but the author
did not: validating deletion against receiver visibility would reject valid work.
It also includes inspect/confirm Restore, Undo/Redo, supplementary/combining
scalars, independent insertions and the explicitly opted-in retain witness.
The bridge retains its explicit retain profile. The subsequent Session-default
revision selects that same policy; historical consume evidence remains separate.

A separate last-gap witness has Alice insert X after ab while Bo concurrently
deletes b. Cam receives the insertion before or after that deletion. Both legal
orders must admit the original gap2 packet and produce aX with identical full
combined state. Counting Cam's current visible births would reject one order.

Twenty-two directed rejection checks preserve exact serialized combined state:
missing prerequisites; omitted birth dependencies; duplicate deletion targets;
unknown deletion targets;
placement without birth; writer/ID mismatch; birth/payload mismatch; omitted
writer predecessor; invalid/boolean gaps; a compound valid birth plus foreign
withdrawal; malformed pairs; attempted caller visibility; changed duplicate;
each of the six resource ceilings; an injected order failure; and an actually terminated order subprocess.

Four scratch mutations run against the unchanged checks:

- validating deletions against the receiver's current view rejects a valid
  concurrent deletion in the retained positive histories;
- publishing the trial before checking the order/digit budget fails the exact
  state-preservation assertion;
- bounding a gap by receiver visibility rejects the valid last-gap packet;
- removing the duplicate deletion-target guard accepts the directed invalid
  packet and fails its unchanged rejection assertion;
- removing the full birth-ID multiset guard permits same-count duplicated or
  foreign IDs in either backend. Both faults must defer as oracle failures,
  preserving the complete joint snapshot.

The writer-counter-order guard is defense in depth, not separately exercised.
For a fresh ID, an ancestral same-writer counter at or above it would require
the candidate's own predecessor-chain entry already to exist; exact/conflicting
duplicate handling occurs earlier. This is a written reachability argument under
this profile's ID and predecessor rules, not another mutation-coverage result.

No mutation switch enters the implementation. The receipt is finite evidence,
not a machine-checked atomicity/convergence theorem. This still does not establish
authentication, general authorization, public IDs, all Session-reachable effect
semantics, ordering-policy adoption or a usable Rust engine. PR9's separate-
prepend interleaving limitation and unadopted replacement order remain intact.

The [pending recovery experiment](../pending-recovery/README.md) adds a bounded
holder for missing/resource/oracle-deferred values. `Deferred` remains a subclass
of `Rejected`; accepted facts and the existing receipt are unchanged. Its caller
must distinguish that disposition from invalidity and from inbox Backpressure.
It is not a selected transport or durable recovery contract.

## explicit FugueMax joint-admission mode

`bash experiments/combined-admission/check.sh --fugue` uses the reviewed
`fugue.mjs` candidate at this existing joint boundary. Default invocation and
`receipt.json` retain the earlier dense-key comparison. The opt-in mode has
its own `fugue-receipt.json`; `--record` regenerates only the selected mode.
No caller-supplied parent/origin fields or new packet language is introduced.
The author basis and visibility are derived from the actual causal effect
facts exactly as above; Node derives and freezes FugueMax placement there.

`Oracle('fugue')` selects the Node backend. `Combined` chooses a matching
`FugueLimits` profile if none is supplied; supplying legacy `Limits` to that
backend rejects instead of silently ignoring its digit ceiling. Shared fact
ceilings remain events128 / births512 / packet8192 bytes / scalars64 / deps64.
The ordering ceiling is **1,536 derived-node parent/origin slots**, exactly three fields per
retained birth (parent, left origin, right origin), including sentinel values.
The nodes are materialized by the order oracle; Combined retains author records
and regenerates the nodes, rather than persisting a Fugue tree. This is a
logical representation metric, redundant with the
current birth ceiling at its default. Its work is to pin final ordering-budget
failure to the same joint commit, not to claim efficient storage. It is not a
byte, heap, stack, CPU, author-snapshot or transient-oracle memory bound, and
the numbers remain unadopted experiment parameters. Legacy key expansion and
its 4,096-digit metric do not describe this representation.

The 46 actual Session views pass in both causal replay orders, with exact
duplicates and cold-state comparison. Warm/cold Session trace production is
also compared byte for byte in this mode. Two added **actual two-writer Session**
histories supply the rejected separate-keystroke prepend witness, with IDs
exchanged: six legal delivery schedules each, yielding a2143b or a4321b and
identical joint snapshots. The paper's three-author Figure 7 is also produced
by actual Sessions: all 16 causal schedules give AXYBC, distinguishing plain
Fugue's AYXBC. That fixture belongs to this three-tag reference domain, not
the proposed two-writer Rust profile. The Session authors already mutated their private
stacks before these packets enter admission: this is **not** the Rust whole-
instance local-call transaction, nor an incremental native sequence engine.

A real Friday→Monday replacement exceeds a reduced ordering-slot ceiling only
after effect and placement trial work. It returns resource deferral, leaves
Friday! visible and the whole accepted tuple unchanged, and preserves the
caller's exact compound packet. Backend-label, birth-count and complete birth-ID
multiset mismatches return oracle deferral without publication; they do not
establish that the packet is invalid. Expected IDs come from the trial's admitted
canonical births, not from a second oracle reply. The five common mutation controls
run in both modes; four additional Fugue controls substitute plain Fugue or remove
the ordering ceiling, backend binding or both birth guards. Each must fail its
intended assertion. A source mutation interrupted before Python's atexit cleanup
may leave a scratch Node module; its exact filename pattern is ignored so ordinary
Git staging cannot accidentally publish that mutant.

The old pending-recovery checkpoint/profile is not extended by this change.
There is no Fugue checkpoint/inbox claim; Inbox explicitly rejects a Fugue
oracle, even if matching FugueLimits are supplied, rather than emitting an
unversioned checkpoint. No ordering policy, public IDs, new-work redo behavior or
release budget is adopted. The [Rust cut](../../docs/rust-transition-cut.md)
now distinguishes the candidate's origin/traversal obligations from the old
key-expansion theorem rather than requiring an equivalence between two orders
that intentionally differ.
