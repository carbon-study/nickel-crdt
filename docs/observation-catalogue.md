# undo observation catalogue

Edition **2026-11-01.1**, 40 questions. [Web questionnaire](https://nickel-undo.shit.yachts/), [complete Markdown scenarios](https://nickel-undo.shit.yachts/undo-questions.md), [browser-compatible blank response](https://nickel-undo.shit.yachts/undo-answers-template.json). The frozen dataset is in [PR2's original edition](https://github.com/carbon-study/nickel-crdt/blob/e220176/questionnaire/public/questions.js). This catalogue indexes that edition; it changes no scenario or option.

## how answers become requirements

Each question is an independent preference probe. Some later questions stipulate an intermediate result instead of deriving it from an earlier answer. Compare by question ID and full scenario, not choice number alone. Preserve respondent explanations and application qualifications. No response is an adopted contract, executable test or proof. No score is computed.

Before turning an answer into a test:

1. State the relevant initial identities, causal order, local item boundaries and selected command. Resolve any missing assumptions with the respondent.
2. Separate desired text from identity, version, stack, anchor and publication observations. A display-only oracle can miss invisible activity.
3. Check the proposed outcome jointly with its undo/redo, delayed-arrival and cold-recovery continuations. Mark conflicts or undecided outcomes explicitly; do not guess missing intermediate answers.
4. Have the policy accepted, then encode a named assertion with a witness-to-contract link and a semantic negative control. Preserve the original response separately from the accepted assertion.

The current collection is a design conversation, not a neutral user study. There are no defaults, but contribution-preserving choices frequently appear first. This can bias responses. Keep this edition stable while people answer. A later edition may randomize display order while retaining stable option identities and export snapshots.

## scenario index

All outcomes remain **pending policy review**. The right column names where an accepted requirement would belong; it does not assert that the current proposal supports every possible answer. V1–V9 refer to [the prospective verifier obligations](api-verification.md#4-prospective-verifier-obligations), all unfulfilled. Registers are deferred and have no selected semantics.

| ID | scenario | decision / prospective obligation |
| --- | --- | --- |
| q01 | whose last edit? | local item selection; V5 |
| q02 | one account, two devices | writer/session versus account; V5/V8 |
| q03 | the top item is invisible | invisible pop and redo; V5 |
| q04 | typing after undo | new primary clears redo; V5 |
| q05 | a peer edits while redo waits | import and redo independence; V5 |
| q06 | a peer inside my insertion | independent insertion preservation; V4/V5 |
| q07 | two deletions of one character | overlapping exact deletion targets; V3/V5 |
| q08 | does dependence imply membership? | dependency versus explicit membership; V3/V5 |
| q09 | a deletion did not see the new character | unseen insertion and removal scope; V3/V4 |
| q10 | same spelling, different insertion | equal spelling versus identity; V3/V5 |
| q11 | hidden creation under a replacement | replacement and hidden creator continuation; V5 |
| q12 | concurrent runs in one gap | concurrent run ordering; V4/V6 |
| q13 | overwriting someone else’s overwrite | register undo effect; future register spec |
| q14 | redo after that register undo | register redo effect; future register spec |
| q15 | both authors undo their register writes | register multi-author continuation; future register spec |
| q16 | two concurrent colors | register winner/alternatives; future register spec |
| q17 | an equal-valued overwrite | equal-valued writes; future register spec |
| q18 | must an invisible undo travel? | invisible event publication; V4/V5/V8 |
| q19 | a late child and an invisible peer undo | late child plus peer activity; V3/V5 |
| q20 | the same undo arrives late | late activity changes current projection; V4/V5 |
| q21 | redoing the invisible item | invisible redo continuation; V5 |
| q22 | redoing the parent afterwards | parent redo continuation; V5 |
| q23 | a consumed invisible item | one consumed item and its opposite; V5 |
| q24 | ordinary typing | editor grouping; explicit library boundaries, V3/V5 |
| q25 | Enter between two edits | editor grouping; explicit library boundaries, V3/V5 |
| q26 | remote import between typing | caller import/group policy; V3/V5 |
| q27 | delayed auto-pair close | explicit delayed membership; V3/V5 |
| q28 | a child completes while its trigger is undone | inactive-trigger child admission; V2/V3 |
| q29 | later does not necessarily mean derived | membership is not elapsed time; V3/V5 |
| q30 | before a hidden character | hidden-before gap; V6 |
| q31 | after a hidden character | hidden-after gap; V6 |
| q32 | typing at a range boundary | anchor affinity; V6 |
| q33 | cursor positions after a cycle | editor selection policy using anchors; V6/V8 |
| q34 | is restored text the same element? | logical identity on restoration; V3/V6 |
| q35 | undo after a reload | snapshot versus session checkpoint; V8 |
| q36 | clear the local history | history clearing versus replicated activity; V5/V8 |
| q37 | when retained history gets too large | admission budget and retention; V2/V8 |
| q38 | an error halfway through a batch | whole-batch rejection; V2 |
| q39 | a cold peer receives equal text | cold semantic recovery; V4/V8 |
| q40 | what would change your mind? | missing scenarios and application qualifications |

## literature comparison, before adoption

- q01–q02 concern selection, which cannot settle the effect questions q06–q23. Prakash/Knister's separation of selection, target shifting and conflicts provides a useful check on that distinction.
- q06–q11 and q27–q31 require a policy for dependencies, explicit children and historical gaps. Neither the word “local” nor a generic counterfactual specifies them. Compare the [groupware and CRDT distinctions](undo-semantics.md) under their actual premises.
- q13–q17 deliberately ask about registers separately. Compare Stewen/Kleppmann's restoration examples with the candidate active-contribution calculation; do not transfer either policy to sequences without an argument.
- q18–q23 and q39 test information needed by a continuation even when current text is identical. A finite response agreeing with an activity policy does not establish convergence or a recoverable protocol.
- q24–q26 and q33 include editor preferences. Keep application timing/selection policy separate from the library mechanisms that accommodate it.

No implementation from the cited work or Nickel was run to produce answers. The catalogue supplies stable names and a review procedure; a complete reference semantics and general algorithm remain the next substantive gate.
