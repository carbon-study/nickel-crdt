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

### store the common prefixes once

Expanding every key would be a bad representation. Even ordinary append gives
key depths 1 through n and n(n+1)/2 stored digits: 528 digits at 32 scalars.
The baseline preserves this failure; it is not a recommended engine layout.

The second interpreter stores the same paths as an ordered tree. An occurrence
stores just its parent occurrence ID (or root) and its one final digit. Its
semantic position is the path of digits from root to that node. Sort each
node's children by digit, then traverse parent before children. This preorder
is exactly the lexicographic order of the expanded paths. Hidden occurrences
stay in the tree; visibility only filters the traversal.

The allocation can also run directly on that representation:

1. In the author's basis tree, find the visible predecessor L and its next
   whole-order node R, exactly as above.
2. Make the first new scalar a child of L, or of root if L is start.
3. If R is already L's child (root's child at start), choose height R.height−1.
   Otherwise choose zero. Use the fresh occurrence identity in either case.
4. Each further scalar is a child of the previous new scalar, with height zero.

Why does this refine the key rule? A node's immediate preorder successor is its
first child, if it has one; otherwise the successor is outside its subtree or
is end. Thus L is a proper prefix of finite R exactly when R is L's first
immediate child. The two height choices match the two key-allocation cases.
New nodes have no existing children, so each later scalar uses the zero case.
By induction the stored parent plus digit expands to the exact baseline key,
and preorder emits the exact baseline sequence. This is a written abstraction
argument, not a machine-checked implementation refinement.

At 32 appends the tree stores 32 digits and 32 parent fields instead of 528
copied digits. More generally there is one order node per occurrence, even
though path depth still reaches n. This counts fields, not encoded bytes or
whole document memory. Identity/height bit widths, retained event bases,
visibility snapshots and Undo facts remain separate costs. The research input
format deliberately copies full author bases and visible sets, so it can still
be quadratic. The interpreter rebuilds basis traversals and sorts children;
no fast incremental edit, serialization budget or usable-scale claim follows.
The test-only abstraction expands paths to compare the two interpreters; it is
not how an engine should store them.

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

**Mutually concurrent insertion events do not interleave.** Here a run means
the text supplied in one insertion event, not a sequence of keystrokes or an
Undo group. This does not settle the broader intended typing-run contract.
A single event's scalar keys share its
first key as a prefix. Two mutually concurrent first keys cannot be prefixes
of one another: generating such an extension would require knowing the other's
fresh digit. Their first differing digit consequently orders every scalar of
one run before every scalar of the other. This says nothing against a later
edit deliberately inserting inside a run; that edit can and should split it.
This argument requires the fresh-name/known-prefix generation rules above, not
merely arbitrary caller-provided keys with a plausible sort order.

Separate backwards-typing events expose the limit: from ab, one writer first
types 1 and then prepends 2 at that spot (a21b); another independently types 3
and prepends 4 (a43b). The merged result is **a2413b**. Every single-event run
still satisfies the argument, but those multi-event typing sequences interleave.
The reference retains this as a limitation, not a passing broader UX guarantee.
Grouping cannot be assumed to fix it after the fact: changing which occurrences
share an Undo item does not change their already-authored positions.

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
| concurrent single-event XY and PQ at the same visible gap in ab | aXYPQb or aPQXYb, by insertion identity order |
| later insert Z inside XY | XY may become XZY; independent concurrent PQ stays a run |
| two independent backwards-typing sequences, each split over two events | a21b and a43b merge to a2413b; broader typing cohesion is not provided |

Friday/Monday is particularly important: restoring the original text does not
mean undoing the replacement. If the candidate is unsuitable here, this is an
explicit placement rule to reject/change, not an implementation accident.
It also distinguishes "a belongs beside b again" from a general promise that
all original words remain adjacent despite edits intentionally made inside them.

## runnable evidence and next boundary

[The reference](../experiments/ordered-gap-reference/README.md) checks twelve
directed outputs and retains the separate prepend limitation. The original
exploration is single-writer: 1,960 author visibility/gap snapshots, not concurrent
histories. It now asserts that a new event immediately follows its visible
predecessor in the whole known order. The visible-right-only variant fails that
assertion in 399 snapshots, rather than merely failing the directed aYXb case.

A separate deterministic family covers 144 histories with two active writers
above an initial writer's ab: all three first gaps, then append, prepend, hide
the own first run or observe the peer's first run. All 792 legal schedules check
key convergence, tree expansion, duplicates and cold reconstruction. All 720
author snapshots check the whole-order gap property; every history checks
per-event cohesion. This remains bounded coverage, not arbitrary concurrency
or a general proof. Two wrong allocation variants and an interleaved-record
oracle control retain concrete failures. Tests do not replace the argument.

Next review this rule and its tree-to-key abstraction against the intended
longer-run/replacement outcomes, then connect visibility to the existing
reference's actual transitions and choose bounded metadata/admission. Then define the
Rust-to-reference abstraction and prove the transitions that actually ship.
General saved anchors, affinity, grouping, private history and budgets remain
outside this order-only artifact; their absence is not delivery of the proposed
experimental crate or verified MVP.
