# Order through actual Undo and Restore effects

This experiment renders the existing Python `Session` after real edits, received
facts, Undo, Redo and inspect/confirm Restore. It combines those actual visible
occurrence IDs with the candidate historical-gap order. It no longer invents a
hidden set independently of the effect interpreter.

From the repository root:

```sh
nix develop --command bash experiments/order-effect-bridge/check.sh
```

Only these bridge checks run. Python uses the hybrid reference's locked shell;
Node uses the root shell. The runner generates full warm and cold traces into a
temporary directory, compares them exactly, checks their ordered views, and
compares the result with `receipt.json`. No services or browser are involved.
For inspection, retain the full input with:

```sh
nix develop ./experiments/hybrid-restoration --command python experiments/order-effect-bridge/trace.py > /tmp/nickel-order-effects.json
nix develop --command node experiments/order-effect-bridge/check.mjs /tmp/nickel-order-effects.json
```

## What crosses the boundary

`trace.py` imports the unchanged `sessions.py` and `model.py`. Immediately before
each insertion, it records the session's actual visible identities and known
insertion ancestors. The fixture supplies a scalar gap index. The resulting
real edit mints the birth identities and scalar payloads. Deletion-only,
withdrawal, release, cancellation and reactivation events mint no order nodes.

`check.mjs` assigns each trusted writer a small numeric tag and bijectively maps
Python birth IDs to the order reference's event/index IDs. It checks scalar
payload equality, one placement per birth and complete coverage of the actual
visible identities. It filters the permanent order using `Doc.visible()` from
the real effect execution. It also checks the separate tree representation and
reverse-order/cold reconstruction of insertion records. This mapping is a
research adapter, not a decision about exact public IDs or their wire encoding.

The second Python run resumes a JSON-copied document and its real private
checkpoint before every session lookup, including between inspecting and
confirming Restore. Subsequent operations must produce the exact same full
trace, not only the same displayed string. Both runs stay within one interpreter
each; no process-restart persistence of issued previews is claimed.

## Retained witnesses

Eight histories yield 46 checked author/peer views:

- explicit Restore of hidden a gives Xab; Undo and fresh-token Redo of Restore;
- creator Undo hides X, Y is inserted, and creator Redo yields aYXb;
- a compound Friday→Monday replacement and Restore yields MondayFriday!,
  retaining Monday; Undo/Redo Restore change only the relevant effects;
- an independent peer's X survives withdrawal of both surrounding births;
- concurrent multi-scalar runs, a supplementary scalar and an unnormalized
  combining sequence retain their exact identities through personal Undo/Redo;
- observed versus unseen concurrent deletion masks, including explicit Restore
  after the unseen deletion arrives;
- the approved retained-skip witness: Undo can reach a skipped deletion after
  the other writer retracts her Restore.

Every expected text is explicit in `trace.py`. MondayFriday! remains a proposed
ordering result, not a product answer inferred from Xab. Simultaneous insertion
runs remain per-event, not a general typing-group cohesion guarantee.

Two wrong interpretations are discriminated by the unchanged text assertions:
ignoring real visibility would fail 24 views; choosing only the visible right
bound fails two views after the real hidden-X/Redo trace. Initially Alice/Bo's
tags happened to make the latter wrong rule pass too. Swapping the writers in
that witness exposed the missing discrimination; no allocation rule changed.
The control is evaluated beside the candidate and required to disagree, not
silently counted as a successful alternative.

## Deliberate limits

This opts into `skip_policy='retain'` explicitly. It does not change the existing
reference's historical consume path. The subsequent Session-default revision
now selects retain too; this bridge keeps its explicit profile binding. New work with pending redo
uses explicit `keep` where needed; no keep/clear product choice is adopted.

The order and effect records are still separate trusted research records. The
adapter does not admit an untrusted combined packet, establish that a remote
visible snapshot is truthful, enforce resource budgets, or prevent a malicious
placement/effect mismatch. Full author bases and replay are expensive. A next
slice must specify and check combined causal admission, including mismatched
birth IDs, omitted dependencies and resource rejection without partial state.

This is finite end-to-end reference evidence, not a Rust implementation, a
machine-checked transition proof, arbitrary delivery exploration or an MVP.
The PR9 order/tree scope and separate-prepend limitation remain unchanged.

## FugueMax candidate adapter

`bash experiments/order-effect-bridge/check.sh --fugue` uses the same trace
producer and expected texts with the stronger `fugue.mjs` interpreter. Its
receipt is `fugue-receipt.json`; the default command and old receipt remain
unchanged. This mode checks the same identity/payload bijection and effect
filtering, plus every causal insertion-event order at each supplied view:
52 deliveries for the existing 46 views. The histories are unchanged, so this
is not exhaustive effect-delivery coverage or additional product approval.
Warm/cold Python inputs remain byte-identical; reverse/cold ordering inputs
preserve all exposed FugueMax metadata. The old dense tree/key equivalence
check only applies to the default interpreter.

See [the conditional retained-node argument](../../docs/fugue-ordering.md) for
what the paper's insertion laws might transfer through hide/reveal. No order
adoption, shared-format change, combined-admission replacement or Rust engine
is performed by this adapter.
