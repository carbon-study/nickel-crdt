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
The older Python consume default and its controls remain unchanged.

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
  packet and fails its unchanged rejection assertion.

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
