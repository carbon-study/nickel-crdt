# checkpoint representation decisions

The current native cut keeps the text fact's author-relative gap and the register
fact's explicit observed bytes and Lamport clock. These are representation
choices for the current API and proof boundary, not assertions that their
replay, storage or copying costs are optimal. Neither choice supplies the open
client refinement or convergence proofs.

## text keeps the author-relative gap

A text fact names the births it deletes, the scalars it inserts, and a position
in its author's pre-edit visible sequence. The receiver reconstructs that
specified author basis before deriving the FugueMax origins. The position must
not be interpreted in the receiver's current visible sequence.

Keep that input contract for the current text cut. The pending semantic
refinement work must connect the actual interpretation to independent
meaning in the author basis. Replacing the position with supplied left/right
origins would add a different input contract: which origin pairs may be
supplied, and how their interpretation relates to that same author-relative
position. Requiring only that both origins occur in the past would not establish
that correspondence.

This choice accepts the current cost of reconstructing author views; it does
not establish that every reconstruction is necessary. Reusing derived origins
or other intermediate results is a separate optimization, with a cache-validity
obligation. It need not require changing the fact's input representation.

The current contracts are in [the edit/admit boundary](rust-edit-admit.md);
[the actual text implementation](../src/edit.rs) contains `author_context` and
the author-basis replay path. This decision does not authorize a gap-to-origins
API migration or change the selected placement semantics.

## registers keep the explicit author assertions

A register write carries a key, new bytes, the bytes its author observed, and a
Lamport clock. The [current validator](../src/register.rs) reconstructs the
selected basis, compares the observed bytes with its read, rejects a value equal
to those observed bytes, and requires the claimed clock to equal the computed
maximum-plus-one result. An offered fact with a wrong assertion is rejected.

Keep those fields for the current native register cut. They are checked
redundancy: the receiver does not trust them as substitutes for reconstructing
the basis. Observed bytes already participate in the counted-write validation
contract; their role is not only hypothetical future Undo support. The clock is
also used by the current priority-selection implementation.

The cost is real: observed bytes can duplicate value-sized data, validation
recomputes the claims, and retained whole-fact equality includes both fields.
Removing either field changes the structured input domain and its rejection
contract. Derivability alone does not make that a behavior-preserving cleanup.
A later replacement must state the new contract and connect it to the retained
history and public outcomes explicitly. Optimizing copies without changing
these fields is a separate question.

There is no stable transport codec delivered by this crate. Keeping the Rust
fact fields does not require a future codec to transmit every derived byte
literally; any such codec still owes reconstruction of the intended facts and
its own validation boundary. No compressed codec or new storage format is
adopted here.

## producer identity does not settle Undo ownership

Undo and redo belong to the user's own captured history. Their decisions stay
frozen: another user's later Undo does not revise, re-enable or retarget them,
and another user's counted intervening write still blocks an older Undo even
after that write is undone. Those outcomes are settled.

Generalizing producer IDs must preserve that rule; it does not authorize
composing Undo across users. Connecting producer streams to the ownership
needed by a future history API is an implementation obligation, not another
outcome question or an extra prerequisite for basic native write/read/replication.
No account/author-tag protocol or native register Undo is delivered here.
