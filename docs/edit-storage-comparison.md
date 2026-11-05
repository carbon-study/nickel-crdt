# fact-storage comparison

This diagnostic answers a design question raised on the native edit/admit cut:
would maintaining ID-sorted facts, instead of canonicalizing them again after
an addition, materially repair the measured latency? It does not adopt a new
library representation or discharge any new proof obligation.

## run it

From the locked default development shell:

```sh
# Focused correctness comparison, normally seconds; no timing runs.
node scripts/compare-edit-storage.mjs .cache/edit-storage
# Manual measurements: six separately capped processes, not a routine CI gate.
node scripts/compare-edit-storage.mjs .cache/edit-storage-profile --profiles
```

The script copies the current crate into its output directory. The reference
copy uses the actual `src/edit.rs`. In the alternative copy, only the
push-plus-canonicalization step in `Replica::plan` changes: a linear merge
inserts the new fact into an already ID-sorted sequence. The public duplicate
and validation gates, private trial clone, interpreter, capacity checks and
publication path stay in place. This is a diagnostic prototype, not an enabled
library option. The source replacements require unique exact matches and the
receipt binds both the original Rust source and the diagnostic script by SHA256.

Both untimed copies run the native tests and the real 150-history/882-schedule
fixture exporter; their entire exported artifacts must match byte for byte.
The alternative also checks all 720 permutations of six storage-level facts:
at every insertion, old facts remain exactly once, the incoming fact appears
exactly once, IDs are strictly sorted, and the result matches the retained
canonicalizer. Those storage inputs are not all valid causal histories.
A deliberately broken alternative that omits old facts must fail native tests.
These are finite checks, not implementation-linked equivalence proofs.
The exported artifact can also be checked with the existing independent
`check-rust-edit-reference.py` oracle; equality to the retained Rust path alone
is not an independent semantic oracle.

## timing boundaries

Only the timing copies instrument the actual `plan` body. Successful additions
record monotonic elapsed differences for identity lookup, `validate_new`, the
trial clone, fact storage, and `interpret`. The storage interval includes the
append plus canonicalization in the reference, or the sorted merge in the
alternative. Both still clone the complete trial; this isolates the storage
change rather than optimizes everything at once.

The existing `edit-profile` example drives actual public author/admit calls and
checks the two instances against its independent sequential ID/scalar list
after every completed pair. Its append/prepend and frontloaded-delete shapes
are unchanged. Its outer call timers include instrumentation overhead and, for
authoring, frontier construction and request copies. The inner phase sums do
not: they omit work outside `plan`, its final capacity/publication tail and
writing the timing line. Error/duplicate paths are not phase-profiled.

Every process has a 45-second cap. A killed run is explicitly incomplete. Its
phase log can include a completed author plan whose receiver did not finish;
the receipt therefore separates completed plans from checked author/admit
pairs. No incomplete run establishes latency at the full ceiling.

## observation

The committed [measurement receipt](measurements/edit-storage.json) binds the
inputs and aggregate phase measurements. This was one sequential run of each
variant/shape on the shared x86_64 Intel i9-12900KF host, without CPU isolation
or counterbalanced variant order. It is not a stable speed comparison, a
worst-case bound, an ARM/phone result, or a memory measurement.

| variant / shape | checked pairs | all measured storage | all measured replay | sum of completed public call times | outcome |
|---|---:|---:|---:|---:|---|
| reference / append | 128 | 19.14 ms | 28.00 s | 28.06 s | complete |
| sorted / append | 128 | 0.95 ms | 28.73 s | 28.77 s | complete |
| reference / prepend | 128 | 19.37 ms | 30.65 s | 30.72 s | complete |
| sorted / prepend | 128 | 0.92 ms | 30.62 s | 30.67 s | complete |
| reference / frontloaded-delete | 62 | 1.51 ms | 44.49 s | — | capped, incomplete |
| sorted / frontloaded-delete | 62 | 0.33 ms | 44.53 s | — | capped, incomplete |

The incomplete reference run contains 125 completed plans, while its alternative
contains 124: neither is a complete 128-event measurement or an exactly equal
amount of completed work. Do not compare their aggregate times as a speedup.
Completed append/prepend final public author/admit calls remain roughly half a
second in both variants. The native tests and permutation test pass; the finite
exported artifacts match exactly and the independent Python/Node oracle passes
on that common artifact. The dropped-old-fact control fails normally.

**Design consequence:** sorting was not the interactive bottleneck on these
histories. Storage got cheaper, but already represented less than 0.07% of the
reference's measured phase time. `interpret` accounted for more than 99.8% of
measured phase time across these runs. The small differences in total wall time
do not establish that either variant is faster overall.

Maintained sorting may still simplify representation invariants. It cannot be
sold as this latency repair, and the diagnostic alternative is not adopted.
The next performance design must avoid reconstructing every author's basis on
every admission. Caching derived event nodes requires a source-linked argument
that their construction depends only on the event's causal past, with exact
agreement to replay; replacing causal closure with version vectors separately
requires a faithful per-writer-prefix argument. Neither follows from sorted IDs
or this measurement. Existing public neutrality, identity and publication
contracts remain requirements for any replacement path. No new machine-checked
content/sortedness, convergence or full-WF claim is made here.
