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

## shared closed-set soundness cut

`PastExact` now owns the checked loop argument that successful shared `past`
retains its roots and stays inside any ID set containing those roots and closed
under the supplied fact-ID/parent callbacks. Both `EditPast` and `RegisterPast`
compose it for `extend_past_preserves`, `past_pass_preserves` and
`past_stays_in_closed_set`. Their concrete statements, mathematical predicates,
refinements and patterns are retained. The text instance uses the checked actual
forwarding-call equations; the register instance explicitly transports its
quantified ID-equality premise.

The control owners follow the implementation knowledge:

- `past-invents-id`, `past-drops-roots` and register `past-extend-unselected`
  now reject in the shared owner. Their old concrete text/register laws remain.
- The historical `past-membership-without-pattern` identifier now removes the
  explicit shared membership call in `PastExact.extend_past_preserves`; both the
  native scan and the alternative `EventGraph` automatic pattern route are
  withheld at that consuming query. The old concrete text pattern is retained.
- `past-skips-passes` keeps the zero-pass fault but fixes its Rust range to
  `usize` and moves its owner to text's bounded-path completeness law. Zero
  passes do not violate closed-set soundness. Its empty-fold case is checked
  before the completeness owner, so an earlier unrelated failure is not credited.
- Three new wrong-argument controls check the retained text forwards separately:
  dropping the incoming selection, skipping the input facts and clearing roots.
  A literal native fixture exercises those proof-only forwards; this is not
  evidence that public runtime execution calls them.
- Separate text/register removal controls require each shared callee contract
  with the corresponding native bodies withheld at the consuming assertions.

Proof-line accounting against the preceding main: text removes67 and adds31;
register removes50 and adds17; the shared module adds185. The net is **+116**
lines, not net retirement of the complete duplicate chain. No Rust forward is
retired by this cut. The remaining exact-ancestry/completeness chain, concrete
text totality/agreement obligations and approved writer-stream slice still need
consolidation before multi-write or another client. No stronger convergence,
admission, Undo or writer-ownership policy follows from this soundness argument.

## shared bounded-path completeness cut

The next composition shares the actual predecessor-expansion, full-pass and
bounded-depth loop arguments in `PastExact`. `EditPast` and `RegisterPast` retain
all their existing theorem statements, recursive reachability definitions and
higher exact-past consumers. Each concrete expansion/pass/depth law now calls the
corresponding generic contract with the native operation and generic callee
withheld at its final query. The register discharges its ID-equality premise;
the text instance also uses checked equations for the actual forwarding calls.

The generic reachability predicate uses positions in the supplied fact slice,
not numeric ID ranks. The concrete predicates are not silently replaced:
`shared_reachable_is_register` and `shared_reachable_is_text` prove equivalence
by depth induction. The text bridge also identifies the generic callback edge
with the existing independent `EditCausal.causal_edge`. These bridges add no
closed-history, uniqueness, root-presence or progress premise to the old laws.
The result is still success-only: the selected IDs cover all predecessor paths
of at most the input fact count. Path shortening, whole exact ancestry, text
success/totality and two-receiver agreement remain in their existing concrete
owners; the generic bounded argument does not replace those proofs.

Control ownership follows the shared implementation argument:

- register `past-extend-never-pushes` and text `past-skips-predecessors` now reject
  in `PastExact.extend_past_covers_predecessors`;
- text's typed zero-pass fault now rejects in the generic bounded-depth owner;
- the historical `past-depth-without-pass-contract` removes the pass contract
  inside that generic depth owner;
- `past-pass-skips-input` is a new typed shared-loop body fault checked in the
  register lane, owned by `PastExact.past_pass_covers_edges`. An empty pass still
  preserves soundness; its empty-fold instance must verify before completeness
  is tested. The earlier foundation failure is refused, not credited;
- each concrete client has separate generic extension/pass/depth contract-removal
  controls and a reachability-bridge removal control. Existing higher path/exact
  contract controls and text forwarding-argument controls remain in place.

Against the preceding soundness cut, text removes131 and adds42 authored proof
lines; registers remove111 and add26; the shared module grows by239. This is **+65**
net authored lines, not a net-size reduction. Concrete predicate compatibility
copies and the remaining path-shortening chain are still visible follow-through.
No native forward is retired. The approved writer-stream slice remains before
multi-write or another client. No native behavior, API, toolchain, budget,
classifier, client totality/agreement or general convergence claim changes.

The bounded query-cost repair keeps these statements and control owners intact.
The unused concrete register `expansion_composes` compatibility theorem needs no
local quantified proof steps: deleting them verifies the same universal claim,
without adding a replacement lemma. The generic depth loop records the checked
pass result in an explicit consuming assertion with the native pass and callee
body withheld before matching on the result. Its removal control must fail
ordinarily at that boundary, rather than spend its budget reopening the loop.
These are proof-body changes, not limit increases or weaker negative evidence.

## shared full-ancestry composition

`PastExact` now contains the finite path-shortening argument and both directions
of successful exactness. The argument maps each path parent to a position in the
fact slice; a repeated position permits cutting a cycle. It uses neither a numeric
ID rank nor a unique-ID or closed-history premise. Both concrete clients retain
their independent path predicates. Structural induction proves each equivalent
to the generic callback path, using the existing checked text-edge and bounded
reachability bridges rather than changing those definitions.

The concrete soundness, short-path coverage, arbitrary-path coverage and exact
closure laws compose these generic contracts at their actual policies. The text
instance also uses the checked equation for its actual native `past` forward.
Native `past` and the generic callee are withheld at the consuming assertions.
The successful constructor exposes the generic exact-result quantifier through
`exact_selection_members`; this is a result projection, not another ancestry
algorithm. A proposed extra ancestor-equivalence helper proved redundant under
removal controls and was deleted without replacement.

The following proof-only concrete internals are retired from both `EditPast`
and `RegisterPast`, with their domains transported to the corresponding generic
instances. They are changes of proof spelling, not deleted semantic obligations:

| old concrete internal | shared replacement |
| --- | --- |
| `ancestor_roots_and_edges` | `PastExact.ancestor_roots_and_edges` |
| `path_extends_reach`, `reach_allows_more_edges` | same names in `PastExact` |
| `path_node`, `drop_edges`, `cut_path_loop` | the same generic list operations |
| `dropped_edge_count`, `cut_path_is_shorter` | the same generic length laws |
| `dropped_path_starts_at_node`, `cutting_repeated_node_preserves_path` | the same generic path-cut laws |
| `path_parent_is_present`, `path_parent_position` | the same generic position witnesses |

No external authored proof consumer names these retired concrete internals. The
independent concrete `causal_path`/`ancestor` and `reachable_within` predicates,
all remaining mathematical definitions and all remaining concrete proof headers
are unchanged. In particular, `fact_id_present` and `parent_fact_position` stay
available to text totality. The old concrete `every_path_has_short_path` claim
also remains as a checked composition. The generic path/reach equivalences give
the interpretation of the retired signatures; no new semantic premise is added.

Historical soundness, bounded-depth, path-shortening and exactness removal
controls follow the argument to its shared owners. Each concrete client adds
separate removals of the shared soundness, short-path, arbitrary-path and exact
contracts, its path-meaning bridge at arbitrary-path coverage, and the successful
result projection. The old text totality and two-receiver agreement controls are
retained. Native shared-loop and actual text-forward argument faults remain
separate from these mathematical/contract controls.

Against the preceding bounded-depth cut, text removes232 and adds100 authored
proof lines; registers remove211 and add81; the shared module adds350 and removes1.
The net is **+87** authored lines. The shared full-ancestry argument is now one
implementation-linked chain, but compatibility predicates and wrappers still
cost space. This is not a net-size-reduction claim. No native Rust forward is
retired here. Generic client totality, text agreement transport and the approved
writer-stream consolidation remain separate follow-through before multi-write
or another client. No admission/progress, convergence, Undo or runtime API claim
is added by this composition.
