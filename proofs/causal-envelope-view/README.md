# focused generic envelope proof

`../CausalEnvelope.lt` checks four universal statements against freshly extracted
actual `src/causal.rs`: explicit peer/counter identity equality, first matching
stored identity (including arbitrary duplicate-ID stores), ordered dependency
sequence equality, and whole-event equality under exact client payload equality.
The classifier returns the actual equality helper's result on that first event.
No graph closure, scheduler, transactional publication, client equality
implementation, text placement or register semantics theorem follows here.

Run from the repository's pinned development shell with the existing
`NICKEL_HAX_BIN`, `NICKEL_PROOF_FSTAR`, `NICKEL_HAX_SOURCE` and
`NICKEL_FSTAR_MODEL_CACHE` set:

```
node scripts/check-causal-envelope.mjs /absolute/output-directory
```

Without an output argument the runner uses `.cache/causal-envelope`. Its permanent
output-location lock is inherited by child processes. Each Rust mode owns its
Cargo target and a second independently extracted native inventory. The healthy
extraction must match the retained focused native file byte-for-byte. The
source/view/native/support hash receipt has a mandatory explicit file inventory.
No old proof views, native manifests, pin, checker limit, model or rejection
classifier is changed.

The default command verifies the tracked source/view receipt; it does not invoke
Latte. Optional `NICKEL_LATTE_BIN=/absolute/latte` performs full local emission and
requires byte equality to this complete tracked view. The actual accepted view
was also opened, parsed, declaration-inspected and emitted through registered
Latte MCP with an explicit revision; that full resource matched the immutable
CLI producer. The registered native manifest does not contain this new module,
so strict symbol lookup against it was deliberately not attempted.

The equality caller withholds native dependency equality and composes the checked
helper contract. Both true and false Boolean outcomes are stated explicitly;
the successful repair suggests that pruning also withholds needed return-typing
facts. The proof relies on the explicit two-case contract, not that diagnosis. The supplied
client equality premise is a logical obligation, not certification of callbacks
or arbitrary Rust aliasing/external effects. Hax extraction/models and the F*
checker remain trusted boundaries.
