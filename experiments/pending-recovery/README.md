# Retain deferred facts and resume them

With a one-event capacity, a replica receiving Alice's `a` first accepts only a;
another receiving Bo's `b` first accepts only b. Dropping the rejected second
packet makes that disagreement permanent. This experiment retains that packet,
round-trips both states through a checkpoint, explicitly raises the capacity,
and admits the original facts. Both then render ab. No command is re-authored.

```sh
# from the repository root
nix develop --command bash experiments/pending-recovery/check.sh
```

Only the recovery checks run. The source uses the existing actual-session traces,
combined admission and Node order interpreter. The runner checks the committed
receipt and scratch mutations that drop pending facts, acknowledge a merely
pending fact, or skip the checkpoint retention bound.
Use `--record` to regenerate the receipt. No services, browsers or full matrix.

## What the caller can do

`Inbox.offer(packet)` either admits the packet, retains it as pending, reports an
exact duplicate, or raises. It reports no success for a value it did not keep.

- **Deferred:** missing prerequisites, an experiment resource ceiling, or an
  unavailable order subprocess. These are typed `Deferred` exceptions with a
  kind, extending `Rejected` for compatibility with the prior reference.
  Catch Deferred before treating Rejected as a semantic invalidity. Reason text
  is diagnostic; the inbox does not classify errors by searching that text.
- **Backpressure:** the inbox's own retention capacity is full. Neither accepted
  facts nor retained facts change. **The caller still owns this packet** and
  must keep it for later delivery; the inbox has not received responsibility.
- **Invalid on first inspection:** ordinary Rejected propagates without staging.
  A deferred packet is not yet a validity verdict. If receiving its prerequisites
  later reveals an invalid effect, the retained entry is marked invalid and kept
  for inspection. `acknowledge_invalid(id)` explicitly removes and returns it.
  No inspection/confirmation UI or proof of human inspection is implied.

`drain()` retries retained non-invalid entries until a pass accepts none. A
successful offer also drains; an already-held duplicate only returns its status.
A changed packet under a held event ID is a conflict, not a corrected retry.
An accepted duplicate never publishes that fact again, though draining other
facts can still change the document.

`promote(limits)` is an **explicit test-profile operation**. It may only increase
or preserve each admission ceiling, then retries. It does not automatically grow
memory or select Nickel's release budgets. `checkpoint()` contains accepted
packets, exact retained packets, their dispositions and both sets of limits.
`resume()` re-admits the accepted prefix and restores pending entries without
re-authoring them; the caller then drains or promotes. Resume needs a functioning
order interpreter and can fail closed without returning an incomplete instance.
This is a trusted-shape JSON checkpoint for the same reference version, not
a migration-safe format, durable filesystem recovery or a hostile decoder. No private Undo stack or process-local preview
issuance handle is stored here.

## Bounded retention, not silent dropping

The default experiment retains at most16 entries and65536 **canonical encoded
packet bytes**, counting invalid entries too. These are supplied test parameters,
not accepted product values, actual heap byte accounting or producer-flow-control
semantics. Accepted-state ceilings remain those of the preceding experiment.
The finite drain loop can accept at most the initial number of retained entries;
it does not spin waiting for absent prerequisites or a larger budget.

The envelope's string event ID is needed for retention and conflict checks.
Pending data is explicitly not yet semantically validated. The input is already
parsed; no streaming decoder, authentication, writer fencing, stable storage,
crash-safe acknowledgement, network resend protocol or garbage collection exists.

Individual combined admissions remain transactional. The whole drain batch is
not one transaction: some ready facts may be accepted while others remain
pending or become invalid. The caller must not interpret pending/Backpressure as
an instruction to erase remote facts. Capacity overflow itself is still **not
convergence**. The two-replica witness only rejoins after retained delivery,
adequate explicit capacity and complete valid facts; it is not a general
liveness or arbitrary-schedule theorem.

## Evidence

All46 recorded views of the eight actual Session histories are delivered in
reverse order under a one-event capacity, with checkpoint/resume after each
offer. After promotion their original texts return. The receipt records202
checkpoint comparisons, not202 independent histories. A separate save/resume
probe runs in two distinct Python processes and fresh Node interpreters, using
a temporary file between them. It reproduces a → ab after the original Python
process has exited; this is not fsync/power-loss or private-session recovery.

Additional directed cases cover:

- replicas accepting different initial subsets, then resuming to ab;
- zero staging slots or bytes returning Backpressure unchanged, followed by an
  explicit capacity increase and successful caller re-offer;
- an actually terminated order subprocess: the fact is retained, checkpointed,
  and admitted using a fresh interpreter;
- a missing prerequisite revealing an invalid deletion, kept until explicit
  acknowledgement, including a conflicting held-ID attempt;
- an Undo authored before an unseen concurrent deletion: resource deferral,
  checkpoint and retry keep its exact original frozen mask. The receiver does
  not extend it to cover the later deletion;
- rejection of capacity decreases without changing the inbox.

Acknowledgement is explicitly refused for missing/resource/oracle-pending facts,
both before and after checkpoint/resume, with exact snapshot preservation. Valid
pending facts still admit after their prerequisite or resource/interpreter
condition is resolved. Separate trusted-shape checkpoint tests lower the saved
slot or byte cap below its retained content and require resume to reject without
changing the original inbox. Both guard-removal mutants survived the old checks;
the new directed cases catch them. No inbox admission or discard rule changed.

The current oracle's `ok:false` means validation failure and is treated as
invalid. Its subprocess/unavailability failures use Deferred instead. If the
oracle ever reports environment or resource failures through `ok:false`, that
classification must change before those outcomes can safely become permanent
invalid entries. This experiment does not establish that future error contract.

The unchanged combined-admission receipt and controls also still pass. This
extends error disposition, not its accepted event language or the Python Session
default. Retain is explicitly opted into by the existing trace generator; no
new-work redo, exact-ID, general placement or release-profile choice is adopted.
No Rust engine, machine proof or usable-MVP claim follows from this experiment.
