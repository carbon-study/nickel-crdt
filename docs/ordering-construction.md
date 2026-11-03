# candidate order: insert before the hidden interval

**Authored research candidate, not an adopted Nickel policy or Rust engine.**
This supplies one finite-history ordering construction and its consequences.
It leaves Undo selection and restoration masks separate: they determine a set
of visible occurrence IDs; this construction orders those IDs. The reference
has no deletion/Undo/Restore transitions, no saved cursor or anchor API, and no
integrated CRDT correctness result. The proposed placement after restoration
below is a recommendation to examine, not an answer attributed to Ren.

## start with the operation

Keep every inserted occurrence in one permanent total order, including hidden
ones. At an insertion's authoring snapshot:

1. Find the visible occurrence just before the requested gap, or the start.
2. Starting immediately after it in the **whole known order**, find the next
   occurrence, hidden or visible, or the end.
3. Allocate the new run strictly between those two permanent positions.
4. Record enough authoring context to reproduce that choice. Receivers do not
   choose the interval again from their current display.

Thus text typed at a collapsed hidden interval goes before that interval.
Changing visibility never reassigns old positions. For Ren's `ab` example,
hiding a leaves the visible gap at the start of b; the next known occurrence
is still hidden a. X goes before a, so making a visible gives **Xab**. The two
q30/q31 histories get the same placement from their same current visible gap.
This witnesses the final order only: the reference does not implement their
retained-cursor histories or promise a general anchor resolution rule.

A small test distinguishes this from looking only for the next *visible*
occurrence. Start with ab, insert X between them, then hide X. Type Y between
the now-visible a and b. The candidate puts Y before hidden X: **aYXb** after
X returns. The wrong visible-right-only variant in the reference gives aXYb.

## an explicit allocation rule

This is a deliberately simple dense-key construction. It is not attributed to
a literature algorithm or claimed novel. Each position is a nonempty finite
sequence of digits. A digit is `(height, writer, counter, scalar-index)`, with
integer height and nonnegative integer identity fields. Compare digits
lexicographically, then compare sequences lexicographically, a proper prefix
coming first. Start is the empty sequence, below every actual position; end is
a separate greatest sentinel. Each `(writer,counter)` names one insertion
with fresh per-scalar indices. Conflicting reuse of that name is invalid.

To allocate between finite L and R (R may be end):

- If L is a proper prefix of finite R, append to L a new digit whose height is
  one less than R's next digit, with the new occurrence's identity fields.
- Otherwise, append to L a digit of height zero with those fresh fields.

For a run, allocate its first scalar in the chosen interval. Repeatedly use the
last new scalar as L and the same R for the rest. This makes every later scalar
key an extension of the run's first key. There is no per-character choice by
receivers and no ordering based on visibility at import time.

The simple allocation is intentionally not a storage recommendation. Even
ordinary append grows keys: n single-scalar appends use depths 1 through n,
so there are n(n+1)/2 stored digits. The executable receipt measures 528 digits
for just 32 scalars. No bounded-memory, logarithmic-operation or usable-size
performance claim follows. A compact representation or different allocation
needs its own refinement argument; replacing keys cannot silently change order.

## finite-history argument and its conditions

Consider a finite, acyclic insertion history with unique insertion names,
downward-closed author bases and fresh scalar indices. Each author's supplied
visibility set is a subset of its basis's occurrences. In the future integrated
model, deriving that visibility set from edit/undo facts is an additional
obligation; accepting an arbitrary set here is not their admission rule.

**An interval always has room, using unbounded mathematical integers.**
If L is a proper prefix of R, the appended height is less than R's first
unmatched height: L < new < R. Otherwise L and R differ at an earlier digit,
so extending L keeps that earlier comparison and gives L < new < R. End has
no upper restriction. Repeating this step puts the whole finite run inside the
original interval in scalar order. The Node reference guards safe integers
and rejects an unrepresentable height; it is not an unbounded integer engine.

**New positions are distinct from all known positions.** L and R were adjacent
in the author's complete known order, and every newly allocated key is strictly
inside that empty interval. It therefore cannot equal a known key. Concurrent
allocations cannot collide either: at their first newly authored digit they
carry different fresh occurrence identities. A descendant of an unknown key
would have to contain that key's fresh digit, which the author cannot obtain by
copying a known prefix or by generating its own distinct identity.

**All finite histories in this domain have one total interpretation.** Process
insertions in any topological order. By induction an insertion's entire basis
already has the same positions; its supplied visible set, gap and allocation
therefore produce the same keys. Processing concurrent insertions earlier does
not change its basis. Sorting the final unique keys gives one total order;
filtering by one fixed visible-ID set gives one displayed sequence. This is an
argument about the order component, conditional on equal visible IDs, not a
proof of convergence for Nickel's full editing/Undo semantics or implementation.

**Known visible gaps are respected.** Every new key lies after the visible
predecessor and before the first known whole-order successor. That successor
is at or before the visible successor. All new scalars therefore appear at
the requested gap in the author's current display. Earlier keys and their
relative comparisons never change. Later visibility changes only filter them.

**Mutually concurrent runs do not interleave.** A run's scalar keys share its
first key as a prefix. Two mutually concurrent first keys cannot be prefixes
of one another: generating such an extension would require knowing the other's
fresh digit. Their first differing digit consequently orders every scalar of
one run before every scalar of the other. This says nothing against a later
edit deliberately inserting inside a run; that edit can and should split it.
This argument requires the fresh-name/known-prefix generation rules above, not
merely arbitrary caller-provided keys with a plausible sort order.

These are written arguments, not machine-checked theorems. There are no new
hax/Latte proofs or Rust transitions in this artifact.

## consequences to test, not silently approve

The reference keeps original IDs and asks what happens when an external
visibility set reveals them again. That ID choice is the experiment's existing
convention, not approval of the still-pending exact-public-ID release contract.

| history | candidate result when hidden originals return |
| --- | --- |
| hide a in ab, type X at start of b | Xab (Ren's settled witness) |
| hide bcd in abcdef, type XY after a | aXYbcdef (new proposed extension) |
| change Friday to Monday before `!`, then reveal original Friday without hiding Monday | MondayFriday! (new proposed extension; no automatic separator) |
| insert peer X between visible a and b, hide/reveal a and b | X while hidden, then aXb |
| concurrent XY and PQ at the same visible gap in ab | aXYPQb or aPQXYb, by insertion identity order |
| later insert Z inside XY | XY may become XZY; independent concurrent PQ stays a run |

Friday/Monday is particularly important: restoring the original text does not
mean undoing the replacement. If the candidate is unsuitable here, this is an
explicit placement rule to reject/change, not an implementation accident.
It also distinguishes "a belongs beside b again" from a general promise that
all original words remain adjacent despite edits intentionally made inside them.

## runnable evidence and next boundary

[The reference](../experiments/ordered-gap-reference/README.md) runs the directed
cases, both relative writer orderings, four legal delivery schedules for the
small branching fixture, duplicate/cold reconstruction checks and 1,960 bounded
author snapshots. Two wrong variants exhibit the hidden-right and receiver-
reselection failures. Passing these tests is not the finite-history argument.

Next reconcile this explicit rule with the intended longer-run/replacement
outcomes, assess a representation that avoids quadratic append keys, and connect
visibility to the existing reference's actual transitions. Then define the
Rust-to-reference abstraction and prove the transitions that actually ship.
General saved anchors, affinity, grouping, private history and budgets remain
outside this order-only artifact; their absence is not delivery of the proposed
experimental crate or verified MVP.
