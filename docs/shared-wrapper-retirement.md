# retiring the migration bridges

`edit::Replica` runs the shared algorithms. a few concrete wrappers are still
production specialization points; others survive only because old theorem terms
and direct helper tests name them. these are different obligations. the cleanup
does not remove a theorem or shrink its domain to make a wrapper disappear.

## current inventory

this inventory concerns the source call graph in `src/edit.rs`, excluding test
modules and explicit extraction roots. a call from an extracted proof bridge is
not evidence that public runtime execution calls that bridge.

| category | concrete names | current purpose |
| --- | --- | --- |
| proof-only graph forwards | `duplicate_events`, `has_fact`, `validate_after`, `extend_past`, `past_pass`, `past` | preserve old graph/admission theorem terms while the shared implementation runs the inner calls |
| proof-only order/filter forwards | `choose_unseen`, `canonical_step`, `select_basis` | preserve old selection/canonicalization/filter terms; shared canonical/basis calls execute their own generic helpers |
| proof-only readiness forward | `ready` | preserve the old direct readiness claim and helper-call control; actual scheduler choice invokes shared readiness |
| legacy envelope classifier fixture | `causal::classify` | unchanged focused arbitrary-payload equality-function claim; no longer called by either real client, which use shared classification |
| executed specializations | `push`, `has_event`, `canonical`, `choose_ready`, `frontier`, `event_basis` | actual text callers use these shared specializations |
| concrete callback policy | `fact_id`, `fact_after`, equality/order/clone/error callbacks, predecessor/forbidden-ancestor callbacks | supplies the text identity, error and whole-fact policies used by generic code |
| concrete interpretation/publication wiring | scheduling/planning callbacks and `Replica::plan` | connects generic scheduling and transactional order to real text validation, replay and limits |

this table is not permission to remove executed callbacks merely to reduce line
count. it also does not promote proof-only names into permanent native APIs.

## deletion sequence

1. first retire the proof-only graph forwards at their owning `EditWellFormed`,
   `EditPast`, `EditPastTotal` and `EditCausal` boundaries. define their old
   mathematical predicates unchanged; replace occurrences of the forwarding
   native term by the exact specialized shared call. preserve parameters,
   refinements, error policy and universal domain. retain a checked compatibility
   equation while callers are moved, then remove that equation with the wrapper.
2. do the same for order/filter terms in `EditAccepted` and `EditBasis`, and
   readiness in `EditSchedule`. a generic replacement of a stronger text law
   needs its actual premises proved; comparison-relative generic base laws alone
   do not replace closure, ranking or provenance.
3. move each direct helper control to the actual specialized call or owning
   shared body. preserve the named semantic fault and exact ordinary rejection;
   test altered actual call arguments separately from altered shared bodies.
   no earlier unrelated failure counts. old `ready` helper-only sensitivity must
   not be reported as public interpreter sensitivity while this is in flight.
4. delete each Rust forwarding function only when no production caller, theorem
   term, helper test or mutation anchor requires it. remove its explicit hax root,
   regenerate the complete actual extraction/views/receipts, and run its owning
   positives plus scoped wrong-body/wrong-argument and callee-dependence controls.
5. run source-boundary review alongside exact-head CI. the exit condition is no
   proof-only native forwarding functions, with old claims transported to actual
   shared calls and controls still testing their intended faults. executed
   specialization callbacks may remain if they do real client work.

the remaining `causal::classify` fixture needs a separate compatibility step:
transport its first-match statement, including its arbitrary supplied payload
equality function, onto the shared classifier with an exact full-event
comparison adapter. preserve all four `CausalEnvelope` claims and their
wrong-body/dependence controls, then delete the old scan and extraction root.
its current isolated proof gate certifies that fixture, not runtime dependence
of the batch client on it. do not drop a checked claim just to delete the file.

these are bounded proof migrations, not a promise that they are already checked
or cost-free. each cut must name the changed claim spelling and preserve the old
claim through an explicit equation; silent theorem weakening is forbidden.

## separate decisions

the public text identity remains Alice/Bo. the writer-identity proposal is not an
implemented or adopted `u64` migration. a shared arbitrary-identity algorithm
needs no such choice to serve both text and the non-text example. the example's
concrete envelope and graph policy do not constitute generic client convergence,
register semantics or a new public document API.
