//! Payload- and identity-generic versions of the edit engine's causal scans.
//! Callers supply identity projection, equality, ordering and error values.
//! Exact-value laws require the supplied clone callback to preserve whole facts.

/// One graph policy: projections/comparisons/copy, then graph errors.
/// Fields in the first group are id, after, id_eq, id_lt, clone_fact, fact_eq.
/// Error fields are internal, missing. Function pointers stay opaque client policy.
pub type GraphOps<F, I, E> = (
    (fn(&F) -> I, fn(&F) -> &[I], fn(&I, &I) -> bool,
     fn(&I, &I) -> bool, fn(&F) -> F, fn(&F, &F) -> bool),
    (fn() -> E, fn() -> E),
);
/// Admission adds predecessor/forbidden and ordered error constructors:
/// duplicate dependency, producer predecessor.
pub type AdmissionOps<I, E> = (
    fn(&I) -> Option<I>, fn(&I, &I) -> bool,
    (fn() -> E, fn() -> E),
);
pub type EventOps<F, I, E> = (GraphOps<F, I, E>, AdmissionOps<I, E>);

/// Build the graph tuple once, preserving its generic function-arrow type in
/// fresh extraction as well as naming the construction arguments in one place.
pub const fn graph_ops<F, I, E>(
    id: fn(&F) -> I, after: fn(&F) -> &[I], id_eq: fn(&I, &I) -> bool,
    id_lt: fn(&I, &I) -> bool, clone_fact: fn(&F) -> F,
    fact_eq: fn(&F, &F) -> bool, internal: fn() -> E, missing: fn() -> E,
) -> GraphOps<F, I, E> {
    ((id, after, id_eq, id_lt, clone_fact, fact_eq), (internal, missing))
}

pub const fn event_ops<F, I, E>(
    graph: GraphOps<F, I, E>, predecessor: fn(&I) -> Option<I>,
    forbidden: fn(&I, &I) -> bool, duplicate_error: fn() -> E,
    predecessor_error: fn() -> E,
) -> EventOps<F, I, E> {
    (graph, (predecessor, forbidden,
        (duplicate_error, predecessor_error)))
}


/// Classify the first stored identity match, preserving storage-order behavior.
/// None is a new identity; Some(true) is exact duplicate; Some(false) conflict.
pub fn classify<F, I, E>(facts: &[F], fact: &F, ops: &GraphOps<F, I, E>) -> Option<bool> {
    let ((id, _, id_eq, _, _, fact_eq), (_, _)) = *ops;
    for i in 0..facts.len() {
        let old = &facts[i];
        if id_eq(&id(old), &id(fact)) {
            return Some(fact_eq(old, fact));
        }
    }
    None
}

pub fn push<T, E>(xs: &mut Vec<T>, value: T, internal: fn() -> E) -> Result<(), E> {
    if xs.len() == usize::MAX {
        return Err(internal());
    }
    xs.push(value);
    Ok(())
}

pub fn has_id<F, I, E>(ids: &[I], wanted: &I, ops: &GraphOps<F, I, E>) -> bool {
    let ((_, _, id_eq, _, _, _), (_, _)) = *ops;
    for i in 0..ids.len() {
        if id_eq(&ids[i], wanted) {
            return true;
        }
    }
    false
}

pub fn duplicate_ids<F, I, E>(xs: &[I], ops: &GraphOps<F, I, E>) -> bool {
    let ((_, _, id_eq, _, _, _), (_, _)) = *ops;
    for i in 0..xs.len() {
        for j in 0..i {
            if id_eq(&xs[i], &xs[j]) {
                return true;
            }
        }
    }
    false
}

pub fn has_fact<F, I, E>(facts: &[F], wanted: &I, ops: &GraphOps<F, I, E>) -> bool {
    let ((id, _, id_eq, _, _, _), (_, _)) = *ops;
    for i in 0..facts.len() {
        if id_eq(&id(&facts[i]), wanted) {
            return true;
        }
    }
    false
}

pub fn validate_after<F, I, E>(facts: &[F], after: &[I], ops: &GraphOps<F, I, E>) -> Result<(), E> {
    let ((_, _, _, _, _, _), (_, missing)) = *ops;
    for i in 0..after.len() {
        if !has_fact(facts, &after[i], ops) {
            return Err(missing());
        }
    }
    Ok(())
}

pub fn extend_past<F, I: Clone, E>(fact: &F, mut selected: Vec<I>, ops: &GraphOps<F, I, E>) -> Result<Vec<I>, E> {
    let ((id, after, _, _, _, _), (internal, _)) = *ops;
    if has_id(&selected, &id(fact), ops) {
        for i in 0..after(fact).len() {
            let predecessor = after(fact)[i].clone();
            if !has_id(&selected, &predecessor, ops) {
                push(&mut selected, predecessor, internal)?;
            }
        }
    }
    Ok(selected)
}

pub fn past_pass<F, I: Clone, E>(facts: &[F], mut selected: Vec<I>, ops: &GraphOps<F, I, E>) -> Result<Vec<I>, E> {
    // Scanning from the end closes a chain of one writer's facts in one pass when
    // they are stored in counter order. Canonical order is by ID, not causal (an
    // earlier-stored alice:1 may depend on bo:2), so mixed chains can take more
    // passes; nothing depends on the order, since past repeats passes until one
    // adds nothing. Scan order changes only the order of the returned IDs; every
    // caller uses them as a set.
    for offset in 0..facts.len() {
        let i = facts.len() - 1 - offset;
        selected = extend_past(&facts[i], selected, ops)?;
    }
    Ok(selected)
}

pub fn past<F, I: Clone, E>(facts: &[F], after_ids: &[I], ops: &GraphOps<F, I, E>) -> Result<Vec<I>, E> {
    let mut selected = after_ids.to_vec();
    validate_after(facts, after_ids, ops)?;
    // A pass that adds no ID is a fixpoint: every later pass returns it unchanged,
    // so the remaining iterations skip the scan.
    let mut closed = false;
    for _ in 0..facts.len() {
        if !closed {
            let before = selected.len();
            selected = past_pass(facts, selected, ops)?;
            closed = selected.len() == before;
        }
    }
    Ok(selected)
}

pub fn choose_unseen<F, I, E>(facts: &[F], out: &[F], ops: &GraphOps<F, I, E>) -> Result<Option<usize>, E> {
    let ((id, _, _, id_lt, _, _), (internal, _)) = *ops;
    let mut chosen = None;
    for j in 0..facts.len() {
        if !has_fact(out, &id(&facts[j]), ops) {
            match chosen {
                None => chosen = Some(j),
                Some(k) => {
                    if k >= facts.len() {
                        return Err(internal());
                    }
                    if id_lt(&id(&facts[j]), &id(&facts[k])) {
                        chosen = Some(j);
                    }
                }
            }
        }
    }
    Ok(chosen)
}

pub fn clone_selected_fact<F>(fact: &F, clone_fact: fn(&F) -> F) -> F {
    clone_fact(fact)
}

pub fn canonical_step<F, I, E>(facts: &[F], mut out: Vec<F>, ops: &GraphOps<F, I, E>) -> Result<Vec<F>, E> {
    let ((_, _, _, _, clone_fact, _), (internal, _)) = *ops;
    let chosen = choose_unseen(facts, &out, ops)?;
    let i = chosen.ok_or(internal())?;
    if i >= facts.len() {
        return Err(internal());
    }
    push(&mut out, clone_selected_fact(&facts[i], clone_fact), internal)?;
    Ok(out)
}

pub fn canonical<F, I, E>(facts: &[F], ops: &GraphOps<F, I, E>) -> Result<Vec<F>, E> {
    let mut out = Vec::new();
    for _ in 0..facts.len() {
        out = canonical_step(facts, out, ops)?;
    }
    Ok(out)
}

pub fn ready<F, I, E>(after: &[I], done: &[I], ops: &GraphOps<F, I, E>) -> bool {
    for i in 0..after.len() {
        if has_id(done, &after[i], ops) {
            // This predecessor has run; keep checking.
        } else {
            return false;
        }
    }
    true
}

pub fn choose_ready<F, I, E>(facts: &[F], done: &[I], ops: &GraphOps<F, I, E>) -> Option<usize> {
    let ((id, after, _, _, _, _), (_, _)) = *ops;
    for i in 0..facts.len() {
        if has_id(done, &id(&facts[i]), ops) {
            // Already scheduled.
        } else if ready(after(&facts[i]), done, ops) {
            return Some(i);
        }
    }
    None
}

pub fn frontier<F, I, E>(facts: &[F], ops: &GraphOps<F, I, E>) -> Result<Vec<I>, E> {
    let ((id, after, _, _, _, _), (internal, _)) = *ops;
    let mut out = Vec::new();
    for f in facts {
        let mut child = false;
        for e in facts {
            if has_id(after(e), &id(f), ops) {
                child = true;
            }
        }
        if !child {
            push(&mut out, id(f), internal)?;
        }
    }
    Ok(out)
}

pub fn select_basis<F, I, E>(facts: &[F], selected: &[I], ops: &GraphOps<F, I, E>) -> Result<Vec<F>, E> {
    let ((id, _, _, _, clone_fact, _), (internal, _)) = *ops;
    let mut basis = Vec::new();
    for i in 0..facts.len() {
        let fact = &facts[i];
        if has_id(selected, &id(fact), ops) {
            push(&mut basis, clone_selected_fact(fact, clone_fact), internal)?;
        }
    }
    Ok(basis)
}

pub fn event_basis<F, I: Clone, E>(facts: &[F], event: &F, ops: &GraphOps<F, I, E>) -> Result<(Vec<I>, Vec<F>), E> {
    let ((_, after, _, _, _, _), (_, _)) = *ops;
    let selected = past(facts, after(event), ops)?;
    let basis = select_basis(facts, &selected, ops)?;
    Ok((selected, basis))
}

/// Shared graph admission, before application-specific payload validation.
/// `forbidden` receives the selected ancestor identity, then the offered one.
pub fn validate_event<F, I: Clone, E>(facts: &[F], fact: &F, ops: &EventOps<F, I, E>) -> Result<Vec<I>, E> {
    let event_ops = ops;
    let ops = &event_ops.0;
    let (predecessor, forbidden, (duplicate_error, predecessor_error)) = event_ops.1;
    let ((id, after, _, _, _, _), (_, _)) = *ops;


    if duplicate_ids(after(fact), ops) {
        return Err(duplicate_error());
    }
    let selected = past(facts, after(fact), ops)?;
    match predecessor(&id(fact)) {
        Some(previous) => {
            if !has_id(&selected, &previous, ops) {
                return Err(predecessor_error());
            }
        }
        None => {}
    }
    for i in 0..facts.len() {
        let e = &facts[i];
        if has_id(&selected, &id(e), ops) && forbidden(&id(e), &id(fact)) {
            return Err(predecessor_error());
        }
    }
    Ok(selected)
}

#[cfg(test)]
mod tests {
    use super::*;

    // A third, string-named producer and opaque payload demonstrate that the
    // shared scans have no dependency on the text client's two-writer IDs.
    #[derive(Clone, Debug, PartialEq, Eq)]
    struct Envelope {
        name: String,
        parents: Vec<String>,
        payload: Vec<u8>,
    }
    fn envelope(name: &str, parents: &[&str], payload: u8) -> Envelope {
        Envelope { name: name.into(), parents: parents.iter().map(|s| (*s).into()).collect(), payload: vec![payload] }
    }
    fn identity(e: &Envelope) -> String { e.name.clone() }
    fn parents(e: &Envelope) -> &[String] { &e.parents }
    fn equal(a: &String, b: &String) -> bool { a == b }
    fn less(a: &String, b: &String) -> bool { a < b }
    fn internal() -> &'static str { "internal" }
    fn missing() -> &'static str { "missing" }
    fn envelope_equal(a: &Envelope, b: &Envelope) -> bool { a == b }
    fn clone_envelope(e: &Envelope) -> Envelope { e.clone() }
    fn duplicate_error() -> &'static str { "duplicate" }
    fn predecessor_error() -> &'static str { "predecessor" }
    fn predecessor(id: &String) -> Option<String> {
        if id == "third:2" { Some("third:1".into()) } else { None }
    }
    fn forbidden(ancestor: &String, current: &String) -> bool {
        current.starts_with("third:") && ancestor == "third:3"
    }
    const OPS: EventOps<Envelope, String, &'static str> = {
        (((identity, parents, equal, less, clone_envelope, envelope_equal), (internal, missing)),
         (predecessor, forbidden, (duplicate_error, predecessor_error)))
    };
    fn validate(facts: &[Envelope], fact: &Envelope) -> Result<Vec<String>, &'static str> {
        validate_event(facts, fact, &OPS)
    }

    #[test]
    fn graph_admission_preserves_error_order_and_producer_arguments() {
        let facts = vec![envelope("third:1", &[], 1), envelope("third:3", &[], 3)];
        let duplicate_missing = envelope("third:2", &["absent", "absent"], 2);
        assert_eq!(validate(&facts, &duplicate_missing), Err("duplicate"));
        assert_eq!(validate(&facts, &envelope("third:2", &["absent"], 2)), Err("missing"));
        assert_eq!(validate(&facts, &envelope("third:2", &[], 2)), Err("predecessor"));
        assert_eq!(validate(&facts, &envelope("third:2", &["third:1"], 2)), Ok(vec!["third:1".into()]));
        assert_eq!(validate(&facts, &envelope("third:2", &["third:1", "third:3"], 2)), Err("predecessor"));
    }

    #[test]
    fn whole_value_copy_uses_the_supplied_callback() {
        fn changed(e: &Envelope) -> Envelope {
            let mut copy = e.clone();
            copy.payload.push(88);
            copy
        }
        let fact = envelope("third:1", &[], 3);
        let mut changed_ops = OPS.0;
        (changed_ops.0).4 = changed;
        assert_eq!(canonical(&[fact.clone()], &changed_ops), Ok(vec![changed(&fact)]));
        assert_eq!(select_basis(&[fact.clone()], &["third:1".into()], &changed_ops), Ok(vec![changed(&fact)]));
    }

    #[test]
    fn classification_uses_first_matching_identity_and_complete_arguments() {
        let exact = envelope("third:1", &["alpha:1"], 3);
        let conflict = envelope("third:1", &["alpha:1"], 4);
        let unrelated = envelope("other:1", &[], 3);
        assert_eq!(classify(&[unrelated.clone()], &exact, &OPS.0), None);
        assert_eq!(classify(&[unrelated, exact.clone(), conflict.clone()], &exact, &OPS.0), Some(true));
        assert_eq!(classify(&[conflict, exact.clone()], &exact, &OPS.0), Some(false));
        let changed_parents = envelope("third:1", &["other:1"], 3);
        assert_eq!(classify(&[changed_parents], &exact, &OPS.0), Some(false));
    }

    #[test]
    fn partial_graph_past_preserves_unresolved_transitive_ids() {
        let facts = vec![envelope("third:1", &["absent:1"], 3), envelope("second:1", &["third:1"], 2)];
        let selected = past(&facts, &["second:1".into()], &OPS.0).unwrap();
        assert_eq!(selected, ["second:1", "third:1", "absent:1"]);
        assert_eq!(past(&facts, &["absent:1".into()], &OPS.0), Err("missing"));
        let (_, basis) = event_basis(&facts, &envelope("caller", &["second:1"], 0), &OPS.0).unwrap();
        assert_eq!(basis, facts);
    }

    #[test]
    fn canonical_is_id_sorted_and_preserves_complete_payloads() {
        let a = envelope("alpha:1", &[], 41);
        let z = envelope("third:1", &["alpha:1"], 99);
        assert_eq!(canonical(&[z.clone(), a.clone()], &OPS.0), Ok(vec![a.clone(), z]));
        // The old canonical algorithm rejects duplicate identities when its
        // fixed number of passes exhausts unseen IDs, even if payloads differ.
        assert_eq!(canonical(&[a, envelope("alpha:1", &[], 42)], &OPS.0), Err("internal"));
    }

    #[test]
    fn ready_scan_and_frontier_keep_storage_order() {
        let facts = vec![envelope("third:1", &["alpha:1"], 3), envelope("second:1", &[], 2), envelope("alpha:1", &[], 1)];
        assert_eq!(choose_ready(&facts, &[], &OPS.0), Some(1));
        assert_eq!(choose_ready(&facts, &["alpha:1".into()], &OPS.0), Some(0));
        assert_eq!(frontier(&facts, &OPS.0), Ok(vec!["third:1".into(), "second:1".into()]));
        assert!(duplicate_ids(&["x".into(), "x".into()], &OPS.0));
        assert!(!duplicate_ids(&["x".into(), "y".into()], &OPS.0));
    }
}
