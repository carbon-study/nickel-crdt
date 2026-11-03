# Combined admission research boundary

The [reference experiment](../experiments/combined-admission/README.md) admits a
parsed effect event and insertion gap as one transaction. It derives placement
visibility from the event's causal effect basis rather than accepting a second,
independent visibility claim. Birth IDs and scalar payloads must agree across
the two interpretations. Rejection leaves effects, order and duplicate records
unchanged.

This is the next integration experiment after the
[order/effect bridge](../experiments/order-effect-bridge/README.md), using the
unchanged Python effect model and JavaScript order construction. The experiment
README specifies packet restrictions, test-only resource ceilings, runnable
checks and failure cases. It is not a selected wire contract or a verified Rust
transition. Resource-pending recovery and real release budgets remain open;
finite accepted-state ceilings do not prove bounded decoder or runtime cost.
