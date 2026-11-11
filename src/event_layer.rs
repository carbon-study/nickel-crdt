//! Payload- and identity-generic versions of the edit engine's causal scans.
//! Callers supply identity projection, equality, ordering and error values.
//! Exact-value laws require the supplied clone callback to preserve whole facts.

/// Classify the first stored identity match, preserving storage-order behavior.
/// None is a new identity; Some(true) is exact duplicate; Some(false) conflict.
pub fn classify<F, I>(facts: &[F], fact: &F, id: fn(&F) -> I,
    id_eq: fn(&I, &I) -> bool, fact_eq: fn(&F, &F) -> bool) -> Option<bool> {
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

pub fn has_id<I>(ids: &[I], wanted: &I, id_eq: fn(&I, &I) -> bool) -> bool {
    for i in 0..ids.len() {
        if id_eq(&ids[i], wanted) {
            return true;
        }
    }
    false
}

pub fn duplicate_ids<I>(xs: &[I], id_eq: fn(&I, &I) -> bool) -> bool {
    for i in 0..xs.len() {
        for j in 0..i {
            if id_eq(&xs[i], &xs[j]) {
                return true;
            }
        }
    }
    false
}

pub fn has_fact<F, I>(facts: &[F], wanted: &I, id: fn(&F) -> I, id_eq: fn(&I, &I) -> bool) -> bool {
    for i in 0..facts.len() {
        if id_eq(&id(&facts[i]), wanted) {
            return true;
        }
    }
    false
}

pub fn validate_after<F, I, E>(facts: &[F], after: &[I], id: fn(&F) -> I,
    id_eq: fn(&I, &I) -> bool, missing: fn() -> E) -> Result<(), E> {
    for i in 0..after.len() {
        if !has_fact(facts, &after[i], id, id_eq) {
            return Err(missing());
        }
    }
    Ok(())
}

pub fn extend_past<F, I: Clone, E>(fact: &F, mut selected: Vec<I>, id: fn(&F) -> I,
    after: fn(&F) -> &[I], id_eq: fn(&I, &I) -> bool, internal: fn() -> E) -> Result<Vec<I>, E> {
    if has_id(&selected, &id(fact), id_eq) {
        for i in 0..after(fact).len() {
            let predecessor = after(fact)[i].clone();
            if !has_id(&selected, &predecessor, id_eq) {
                push(&mut selected, predecessor, internal)?;
            }
        }
    }
    Ok(selected)
}

pub fn past_pass<F, I: Clone, E>(facts: &[F], mut selected: Vec<I>, id: fn(&F) -> I,
    after: fn(&F) -> &[I], id_eq: fn(&I, &I) -> bool, internal: fn() -> E) -> Result<Vec<I>, E> {
    for i in 0..facts.len() {
        selected = extend_past(&facts[i], selected, id, after, id_eq, internal)?;
    }
    Ok(selected)
}

pub fn past<F, I: Clone, E>(facts: &[F], after_ids: &[I], id: fn(&F) -> I,
    after: fn(&F) -> &[I], id_eq: fn(&I, &I) -> bool, internal: fn() -> E,
    missing: fn() -> E) -> Result<Vec<I>, E> {
    let mut selected = after_ids.to_vec();
    validate_after(facts, after_ids, id, id_eq, missing)?;
    for _ in 0..facts.len() {
        selected = past_pass(facts, selected, id, after, id_eq, internal)?;
    }
    Ok(selected)
}

pub fn choose_unseen<F, I, E>(facts: &[F], out: &[F], id: fn(&F) -> I,
    id_eq: fn(&I, &I) -> bool, id_lt: fn(&I, &I) -> bool, internal: fn() -> E) -> Result<Option<usize>, E> {
    let mut chosen = None;
    for j in 0..facts.len() {
        if !has_fact(out, &id(&facts[j]), id, id_eq) {
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

pub fn canonical_step<F, I, E>(facts: &[F], mut out: Vec<F>, id: fn(&F) -> I,
    id_eq: fn(&I, &I) -> bool, id_lt: fn(&I, &I) -> bool, internal: fn() -> E, clone_fact: fn(&F) -> F) -> Result<Vec<F>, E> {
    let chosen = choose_unseen(facts, &out, id, id_eq, id_lt, internal)?;
    let i = chosen.ok_or(internal())?;
    if i >= facts.len() {
        return Err(internal());
    }
    push(&mut out, clone_selected_fact(&facts[i], clone_fact), internal)?;
    Ok(out)
}

pub fn canonical<F, I, E>(facts: &[F], id: fn(&F) -> I,
    id_eq: fn(&I, &I) -> bool, id_lt: fn(&I, &I) -> bool, internal: fn() -> E, clone_fact: fn(&F) -> F) -> Result<Vec<F>, E> {
    let mut out = Vec::new();
    for _ in 0..facts.len() {
        out = canonical_step(facts, out, id, id_eq, id_lt, internal, clone_fact)?;
    }
    Ok(out)
}

pub fn ready<I>(after: &[I], done: &[I], id_eq: fn(&I, &I) -> bool) -> bool {
    for i in 0..after.len() {
        if has_id(done, &after[i], id_eq) {
            // This predecessor has run; keep checking.
        } else {
            return false;
        }
    }
    true
}

pub fn choose_ready<F, I>(facts: &[F], done: &[I], id: fn(&F) -> I,
    after: fn(&F) -> &[I], id_eq: fn(&I, &I) -> bool) -> Option<usize> {
    for i in 0..facts.len() {
        if has_id(done, &id(&facts[i]), id_eq) {
            // Already scheduled.
        } else if ready(after(&facts[i]), done, id_eq) {
            return Some(i);
        }
    }
    None
}

pub fn frontier<F, I, E>(facts: &[F], id: fn(&F) -> I,
    after: fn(&F) -> &[I], id_eq: fn(&I, &I) -> bool, internal: fn() -> E) -> Result<Vec<I>, E> {
    let mut out = Vec::new();
    for f in facts {
        let mut child = false;
        for e in facts {
            if has_id(after(e), &id(f), id_eq) {
                child = true;
            }
        }
        if !child {
            push(&mut out, id(f), internal)?;
        }
    }
    Ok(out)
}

pub fn select_basis<F, I, E>(facts: &[F], selected: &[I], id: fn(&F) -> I,
    id_eq: fn(&I, &I) -> bool, internal: fn() -> E, clone_fact: fn(&F) -> F) -> Result<Vec<F>, E> {
    let mut basis = Vec::new();
    for i in 0..facts.len() {
        let fact = &facts[i];
        if has_id(selected, &id(fact), id_eq) {
            push(&mut basis, clone_selected_fact(fact, clone_fact), internal)?;
        }
    }
    Ok(basis)
}

pub fn event_basis<F, I: Clone, E>(facts: &[F], event: &F, id: fn(&F) -> I,
    after: fn(&F) -> &[I], id_eq: fn(&I, &I) -> bool, internal: fn() -> E,
    missing: fn() -> E, clone_fact: fn(&F) -> F) -> Result<(Vec<I>, Vec<F>), E> {
    let selected = past(facts, after(event), id, after, id_eq, internal, missing)?;
    let basis = select_basis(facts, &selected, id, id_eq, internal, clone_fact)?;
    Ok((selected, basis))
}

/// Shared graph admission, before application-specific payload validation.
/// `forbidden` receives the selected ancestor identity, then the offered one.
pub fn validate_event<F, I: Clone, E>(facts: &[F], fact: &F,
    events_limit: usize, dependencies_limit: usize,
    id: fn(&F) -> I, after: fn(&F) -> &[I], id_eq: fn(&I, &I) -> bool,
    predecessor: fn(&I) -> Option<I>, forbidden: fn(&I, &I) -> bool,
    event_capacity: fn() -> E, dep_capacity: fn() -> E,
    duplicate_error: fn() -> E, predecessor_error: fn() -> E,
    internal: fn() -> E, missing: fn() -> E) -> Result<Vec<I>, E> {
    if facts.len() >= events_limit {
        return Err(event_capacity());
    }
    if after(fact).len() > dependencies_limit {
        return Err(dep_capacity());
    }
    if duplicate_ids(after(fact), id_eq) {
        return Err(duplicate_error());
    }
    let selected = past(facts, after(fact), id, after, id_eq, internal, missing)?;
    match predecessor(&id(fact)) {
        Some(previous) => {
            if !has_id(&selected, &previous, id_eq) {
                return Err(predecessor_error());
            }
        }
        None => {}
    }
    for i in 0..facts.len() {
        let e = &facts[i];
        if has_id(&selected, &id(e), id_eq) && forbidden(&id(e), &id(fact)) {
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
    fn event_capacity() -> &'static str { "events" }
    fn dep_capacity() -> &'static str { "dependencies" }
    fn duplicate_error() -> &'static str { "duplicate" }
    fn predecessor_error() -> &'static str { "predecessor" }
    fn predecessor(id: &String) -> Option<String> {
        if id == "third:2" { Some("third:1".into()) } else { None }
    }
    fn forbidden(ancestor: &String, current: &String) -> bool {
        current.starts_with("third:") && ancestor == "third:3"
    }
    fn validate(facts: &[Envelope], fact: &Envelope, events: usize, dependencies: usize) -> Result<Vec<String>, &'static str> {
        validate_event(facts, fact, events, dependencies, identity, parents, equal,
            predecessor, forbidden, event_capacity, dep_capacity, duplicate_error,
            predecessor_error, internal, missing)
    }

    #[test]
    fn graph_admission_preserves_error_order_and_producer_arguments() {
        let facts = vec![envelope("third:1", &[], 1), envelope("third:3", &[], 3)];
        let duplicate_missing = envelope("third:2", &["absent", "absent"], 2);
        assert_eq!(validate(&facts, &duplicate_missing, 2, 0), Err("events"));
        assert_eq!(validate(&facts, &duplicate_missing, 3, 1), Err("dependencies"));
        assert_eq!(validate(&facts, &duplicate_missing, 3, 2), Err("duplicate"));
        assert_eq!(validate(&facts, &envelope("third:2", &["absent"], 2), 3, 2), Err("missing"));
        assert_eq!(validate(&facts, &envelope("third:2", &[], 2), 3, 2), Err("predecessor"));
        assert_eq!(validate(&facts, &envelope("third:2", &["third:1"], 2), 3, 2), Ok(vec!["third:1".into()]));
        assert_eq!(validate(&facts, &envelope("third:2", &["third:1", "third:3"], 2), 3, 2), Err("predecessor"));
    }

    #[test]
    fn whole_value_copy_uses_the_supplied_callback() {
        fn changed(e: &Envelope) -> Envelope {
            let mut copy = e.clone();
            copy.payload.push(88);
            copy
        }
        let fact = envelope("third:1", &[], 3);
        assert_eq!(canonical(&[fact.clone()], identity, equal, less, internal, changed), Ok(vec![changed(&fact)]));
        assert_eq!(select_basis(&[fact.clone()], &["third:1".into()], identity, equal, internal, changed), Ok(vec![changed(&fact)]));
    }

    #[test]
    fn classification_uses_first_matching_identity_and_complete_arguments() {
        let exact = envelope("third:1", &["alpha:1"], 3);
        let conflict = envelope("third:1", &["alpha:1"], 4);
        let unrelated = envelope("other:1", &[], 3);
        assert_eq!(classify(&[unrelated.clone()], &exact, identity, equal, envelope_equal), None);
        assert_eq!(classify(&[unrelated, exact.clone(), conflict.clone()], &exact, identity, equal, envelope_equal), Some(true));
        assert_eq!(classify(&[conflict, exact.clone()], &exact, identity, equal, envelope_equal), Some(false));
        let changed_parents = envelope("third:1", &["other:1"], 3);
        assert_eq!(classify(&[changed_parents], &exact, identity, equal, envelope_equal), Some(false));
    }

    #[test]
    fn partial_graph_past_preserves_unresolved_transitive_ids() {
        let facts = vec![envelope("third:1", &["absent:1"], 3), envelope("second:1", &["third:1"], 2)];
        let selected = past(&facts, &["second:1".into()], identity, parents, equal, internal, missing).unwrap();
        assert_eq!(selected, ["second:1", "third:1", "absent:1"]);
        assert_eq!(past(&facts, &["absent:1".into()], identity, parents, equal, internal, missing), Err("missing"));
        let (_, basis) = event_basis(&facts, &envelope("caller", &["second:1"], 0), identity, parents, equal, internal, missing, clone_envelope).unwrap();
        assert_eq!(basis, facts);
    }

    #[test]
    fn canonical_is_id_sorted_and_preserves_complete_payloads() {
        let a = envelope("alpha:1", &[], 41);
        let z = envelope("third:1", &["alpha:1"], 99);
        assert_eq!(canonical(&[z.clone(), a.clone()], identity, equal, less, internal, clone_envelope), Ok(vec![a.clone(), z]));
        // The old canonical algorithm rejects duplicate identities when its
        // fixed number of passes exhausts unseen IDs, even if payloads differ.
        assert_eq!(canonical(&[a, envelope("alpha:1", &[], 42)], identity, equal, less, internal, clone_envelope), Err("internal"));
    }

    #[test]
    fn ready_scan_and_frontier_keep_storage_order() {
        let facts = vec![envelope("third:1", &["alpha:1"], 3), envelope("second:1", &[], 2), envelope("alpha:1", &[], 1)];
        assert_eq!(choose_ready(&facts, &[], identity, parents, equal), Some(1));
        assert_eq!(choose_ready(&facts, &["alpha:1".into()], identity, parents, equal), Some(0));
        assert_eq!(frontier(&facts, identity, parents, equal, internal), Ok(vec!["third:1".into(), "second:1".into()]));
        assert!(duplicate_ids(&["x".into(), "x".into()], equal));
        assert!(!duplicate_ids(&["x".into(), "y".into()], equal));
    }
}
