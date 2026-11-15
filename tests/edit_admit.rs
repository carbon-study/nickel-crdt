use nickel_crdt::edit::*;
fn new(writer: Option<Writer>) -> Replica {
    let r = Replica::new(writer).unwrap();
    assert_unique(&r);
    r
}
// Public-state witness for the proved accepted-ID invariant.
fn assert_unique(r: &Replica) {
    assert_causally_closed(r);
    assert!(
        r.facts().windows(2).all(|pair| pair[0].id < pair[1].id),
        "accepted facts must be in strict event-ID order"
    );
    for (i, fact) in r.facts().iter().enumerate() {
        for old in &r.facts()[..i] {
            assert_ne!(fact.id, old.id, "duplicate accepted event ID");
        }
    }
}
// Exact public publication, independently checking whole facts rather than IDs.
fn assert_publication(before: &[Fact], fact: &Fact, after: &[Fact]) {
    assert_eq!(after.len(), before.len() + 1);
    for old in before {
        assert!(after.contains(old), "old fact changed or lost");
    }
    assert!(after.contains(fact), "incoming fact changed or lost");
    for accepted in after {
        assert!(
            accepted == fact || before.contains(accepted),
            "invented fact"
        );
    }
}
fn scalars(s: &str) -> Vec<u32> {
    s.chars().map(u32::from).collect()
}
fn text(r: &Replica) -> String {
    r.observe()
        .unwrap()
        .iter()
        .map(|(_, s)| char::from_u32(*s).unwrap())
        .collect()
}
fn edit(r: Replica, gap: usize, s: &str, delete: Vec<BirthId>) -> (Replica, Fact) {
    let before = r.facts().to_vec();
    let (r, result) = r.edit(gap, scalars(s), delete);
    assert_unique(&r);
    let Local::Authored(f) = result.unwrap() else {
        panic!("unexpected empty")
    };
    assert_publication(&before, &f, r.facts());
    (r, f)
}
fn receive(r: Replica, f: &Fact) -> Replica {
    let before = r.facts().to_vec();
    let (r, result) = r.receive(f);
    assert_unique(&r);
    assert_eq!(result, Ok(Admission::Added));
    assert_publication(&before, f, r.facts());
    r
}
#[test]
fn two_instances_replace_duplicate_conflict_and_empty() {
    let (a, root) = edit(new(Some(Writer::Alice)), 0, "ab", vec![]);
    let b = receive(new(Some(Writer::Bo)), &root);
    assert_eq!(b.next_counter(), 1, "admission changed private allocator");
    let victim = b.observe().unwrap()[0].0;
    let (b, replacement) = edit(b, 0, "X", vec![victim]);
    let a = receive(a, &replacement);
    assert_eq!(a.observe(), b.observe());
    assert_eq!(text(&a), "Xb");
    let before = a.clone();
    let (a, result) = a.receive(&replacement);
    assert_eq!(result, Ok(Admission::Duplicate));
    assert_eq!(a, before);
    let mut changed = replacement.clone();
    changed.gap = Some(1);
    let (a, result) = a.receive(&changed);
    assert_eq!(result, Err(Error::Invalid(Invalid::Conflict)));
    assert_eq!(a, before);
    let (a, result) = a.edit(0, vec![], vec![]);
    assert_eq!(result, Ok(Local::Empty));
    assert_eq!(a, before);
}
#[test]
fn author_last_gap_not_receiver_visibility() {
    let (a, root) = edit(new(Some(Writer::Alice)), 0, "ab", vec![]);
    let b = receive(new(Some(Writer::Bo)), &root);
    let (_, x) = edit(a, 2, "X", vec![]);
    let victim = b.observe().unwrap()[1].0;
    let (_, deletion) = edit(b, 0, "", vec![victim]);
    let mut observations = Vec::new();
    for schedule in [[&root, &x, &deletion], [&root, &deletion, &x]] {
        let mut cam = new(None);
        for fact in schedule {
            cam = receive(cam, fact);
        }
        assert_eq!(text(&cam), "aX");
        observations.push(cam);
    }
    // Structural replay agreement: canonicalization chooses one internal order.
    // The fixed text above discriminates placement; this equality alone does not.
    assert_eq!(observations[0], observations[1]);
}
fn schedules(prefix: Vec<Fact>, remaining: Vec<Fact>, out: &mut Vec<Vec<Fact>>) {
    if remaining.is_empty() {
        out.push(prefix);
        return;
    }
    for i in 0..remaining.len() {
        if remaining[i]
            .after
            .iter()
            .all(|id| prefix.iter().any(|f| f.id == *id))
        {
            let mut rest = remaining.clone();
            let f = rest.remove(i);
            let mut next = prefix.clone();
            next.push(f);
            schedules(next, rest, out);
        }
    }
}
#[test]
fn multi_event_prepend_runs_all_causal_orders() {
    let (a, root) = edit(new(Some(Writer::Alice)), 0, "ab", vec![]);
    let b = receive(new(Some(Writer::Bo)), &root);
    let (a, one) = edit(a, 1, "1", vec![]);
    let (_, two) = edit(a, 1, "2", vec![]);
    let (b, three) = edit(b, 1, "3", vec![]);
    let (_, four) = edit(b, 1, "4", vec![]);
    let mut orders = Vec::new();
    schedules(vec![], vec![root, one, two, three, four], &mut orders);
    assert_eq!(orders.len(), 6);
    // Arrival permutations all feed the same deterministic canonical replay.
    // The fixed a2143b assertion is the independent placement expectation here.
    let mut observed = None;
    for schedule in orders {
        let mut r = new(None);
        for fact in schedule {
            r = receive(r, &fact)
        }
        assert_eq!(text(&r), "a2143b");
        if let Some(old) = &observed {
            assert_eq!(old, &r)
        } else {
            observed = Some(r)
        }
    }
}
#[test]
fn scalar_preservation_and_invalidity_are_atomic() {
    let (a, f) = edit(new(Some(Writer::Alice)), 0, "\0\r\n\u{feff}😀𝄞é", vec![]);
    let b = receive(new(Some(Writer::Bo)), &f);
    assert_eq!(text(&a), "\0\r\n\u{feff}😀𝄞é");
    assert_eq!(a.observe(), b.observe());
    let before = a.clone();
    let (a, result) = a.edit(1, vec![0xd800], vec![]);
    assert_eq!(result, Err(Error::Invalid(Invalid::Scalar)));
    assert_eq!(a, before);
    let (a, result) = a.edit(99, vec![88], vec![]);
    assert_eq!(result, Err(Error::Invalid(Invalid::Gap)));
    assert_eq!(a, before);
}
#[test]
fn replacement_is_not_blocked_by_former_ordering_budget() {
    let r = Replica::new(Some(Writer::Alice)).unwrap();
    let (r, _) = edit(r, 0, "Friday!", vec![]);
    let delete = r.observe().unwrap()[..6]
        .iter()
        .map(|(id, _)| *id)
        .collect();
    let (r, result) = r.edit(0, scalars("Monday"), delete);
    assert!(matches!(result, Ok(Local::Authored(_))));
    assert_eq!(text(&r), "Monday!");
}
#[test]
fn missing_prerequisite_returns_unchanged_owned_state() {
    let (a, root) = edit(new(Some(Writer::Alice)), 0, "ab", vec![]);
    let (_, later) = edit(a, 2, "X", vec![]);
    let r = new(None);
    let before = r.clone();
    let (r, result) = r.receive(&later);
    assert_eq!(result, Err(Error::Missing));
    assert_eq!(r, before);
    let r = receive(r, &root);
    let r = receive(r, &later);
    assert_eq!(text(&r), "abX");
    let low = Replica::new(
        None)
    .unwrap();
    let (low, result) = low.receive(&root);
    assert_eq!(result, Ok(Admission::Added));
    assert_eq!(text(&low), "ab");
}

#[test]
fn authored_fact_replays_the_same_complete_commit() {
    let mut local = new(Some(Writer::Alice));
    let mut remote = new(Some(Writer::Bo));
    for (gap, inserted, remove_index, expected) in [
        (0, "abc", None, "abc"),
        (2, "X😀", Some(1), "aX😀c"),
        (0, "", Some(0), "X😀c"),
        (3, "Z", None, "X😀cZ"),
    ] {
        let before = local.clone();
        let deleted = remove_index
            .map(|i| vec![before.observe().unwrap()[i].0])
            .unwrap_or_default();
        let (next, fact) = edit(local, gap, inserted, deleted.clone());
        assert_eq!(fact.insert, scalars(inserted));
        assert_eq!(fact.delete, deleted);
        assert_eq!(fact.gap, if inserted.is_empty() { None } else { Some(gap) });
        assert_eq!(fact.id.writer, Writer::Alice);
        assert_eq!(fact.id.counter, before.next_counter());
        remote = receive(remote, &fact);
        assert_eq!(next.facts(), remote.facts());
        assert_eq!(next.whole(), remote.whole());
        assert_eq!(next.observe(), remote.observe());
        assert_eq!(text(&next), expected);
        assert_eq!(text(&remote), expected);
        assert_eq!(remote.next_counter(), 1);
        let imported = receive(before.clone(), &fact);
        assert_eq!(next.facts(), imported.facts());
        assert_eq!(next.whole(), imported.whole());
        assert_eq!(next.observe(), imported.observe());
        assert_eq!(imported.next_counter(), before.next_counter());
        assert_eq!(next.next_counter(), before.next_counter() + 1);
        local = next;
    }
}

#[test]
fn identity_gate_checks_every_field_and_later_members() {
    let limited = Replica::new(
        Some(Writer::Alice))
    .unwrap();
    let (a, root) = edit(limited, 0, "ab", vec![]);
    let victim = a.observe().unwrap()[0].0;
    let (a, later) = edit(a, 1, "X", vec![victim]);
    // Known facts are checked before capacity or any new-fact validation.
    for known in [&root, &later] {
        let (next, result) = a.clone().receive(known);
        assert_eq!(result, Ok(Admission::Duplicate));
        assert_eq!(next, a);
    }
    let mut variants = Vec::new();
    let mut changed = later.clone();
    changed.after.clear();
    variants.push(changed);
    let mut changed = later.clone();
    changed.insert = scalars("Y");
    variants.push(changed);
    let mut changed = later.clone();
    changed.delete.clear();
    variants.push(changed);
    let mut changed = later.clone();
    changed.gap = Some(0);
    variants.push(changed);
    for changed in variants {
        let (next, result) = a.clone().receive(&changed);
        assert_eq!(result, Err(Error::Invalid(Invalid::Conflict)));
        assert_eq!(next, a);
    }
    for counter in [0, 9_007_199_254_740_992] {
        let mut bad = later.clone();
        bad.id.counter = counter;
        let (next, result) = a.clone().receive(&bad);
        assert_eq!(result, Err(Error::Invalid(Invalid::Counter)));
        assert_eq!(next, a);
    }
}

#[test]
fn successful_permuted_admissions_publish_identical_facts_and_tree() {
    let (alice, a1) = edit(new(Some(Writer::Alice)), 0, "a", vec![]);
    let (_, a2) = edit(alice, 1, "b", vec![]);
    let (_, b1) = edit(new(Some(Writer::Bo)), 0, "x", vec![]);
    let schedules = [[&a1, &a2, &b1], [&a1, &b1, &a2], [&b1, &a1, &a2]];
    let mut results = vec![];
    for schedule in schedules {
        let mut replica = new(None);
        for fact in schedule {
            replica = receive(replica, fact);
        }
        assert_eq!(replica.facts(), &[a1.clone(), a2.clone(), b1.clone()]);
        assert_eq!(replica.whole().unwrap().len(), 3);
        assert_eq!(replica.observe().unwrap().len(), 3);
        results.push(replica);
    }
    for replica in &results[1..] {
        assert_eq!(replica.facts(), results[0].facts());
        assert_eq!(replica.whole(), results[0].whole());
        assert_eq!(replica.observe(), results[0].observe());
    }
}

#[test]
fn scalar_boundaries_and_late_invalid_payload_are_transactional() {
    let values = [0, 0xd7ff, 0xe000, 0x10ffff];
    let (a, fact) = edit(
        new(Some(Writer::Alice)),
        0,
        &values
            .iter()
            .map(|&v| char::from_u32(v).unwrap())
            .collect::<String>(),
        vec![],
    );
    assert_eq!(fact.insert, values);
    let b = receive(new(None), &fact);
    assert_eq!(a.observe(), b.observe());
    for scalar in [0xd800, 0xdfff, 0x110000, u32::MAX] {
        let before = new(Some(Writer::Alice));
        let (after, result) = before.clone().edit(0, vec![0x61, scalar], vec![]);
        assert_eq!(result, Err(Error::Invalid(Invalid::Scalar)));
        assert_eq!(after, before);
        let malformed = Fact {
            id: EventId {
                writer: Writer::Bo,
                counter: 1,
            },
            after: vec![],
            insert: vec![0x61, scalar],
            delete: vec![],
            gap: Some(0),
        };
        for observer in [new(None), receive(new(None), &fact)] {
            let (after, result) = observer.clone().receive(&malformed);
            assert_eq!(result, Err(Error::Invalid(Invalid::Scalar)));
            assert_eq!(after, observer);
        }
    }
}

// Direct-reference closure is checked separately from text and event-ID order.
fn assert_causally_closed(r: &Replica) {
    for fact in r.facts() {
        for id in &fact.after {
            assert!(
                r.facts().iter().any(|old| old.id == *id),
                "dangling direct dependency"
            );
        }
    }
}
#[test]
fn direct_dependency_guard_checks_later_ids_and_keeps_missing_retry_exact() {
    let (a, root) = edit(new(Some(Writer::Alice)), 0, "a", vec![]);
    let (b, other) = edit(new(Some(Writer::Bo)), 0, "b", vec![]);
    let r = receive(new(None), &root);
    let before = r.clone();
    let offered = Fact {
        id: EventId {
            writer: Writer::Alice,
            counter: 2,
        },
        after: vec![root.id, other.id],
        insert: vec![],
        delete: vec![],
        gap: None,
    };
    let (r, result) = r.receive(&offered);
    assert_eq!(result, Err(Error::Missing));
    assert_eq!(r, before);
    let r = receive(r, &other);
    let r = receive(r, &offered);
    assert_causally_closed(&r);
    assert_eq!(r.facts().len(), 3);
    // Both producer histories remain independently valid and nonempty.
    assert_causally_closed(&a);
    assert_causally_closed(&b);
}
#[test]
fn repeated_dependency_is_rejected_before_closure() {
    // Bo's fact names Alice's root twice: public validation must reject it as a
    // duplicate dependency, leaving the receiver unchanged.
    let (a, root) = edit(new(Some(Writer::Alice)), 0, "a", vec![]);
    let b = receive(new(Some(Writer::Bo)), &root);
    let (_, reply) = edit(b, 1, "b", vec![]);
    assert_eq!(reply.after, vec![root.id], "fixture expects one direct dependency");
    let mut repeated = reply.clone();
    repeated.after = vec![root.id, root.id];
    let before = a.clone();
    let (a, result) = a.receive(&repeated);
    assert_eq!(result, Err(Error::Invalid(Invalid::DependencyDuplicate)));
    assert_eq!(a, before);
    // The single-dependency fact is still admitted.
    receive(a, &reply);
}
