use nickel_crdt::edit::*;
fn new(writer: Option<Writer>) -> Replica {
    let r = Replica::new(writer, Limits::default()).unwrap();
    assert_unique(&r);
    r
}
// Public-state witness for the proved accepted-ID invariant.
fn assert_unique(r: &Replica) {
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
fn replacement_final_budget_failure_keeps_everything() {
    let limits = Limits {
        ordering_links: 21,
        ..Limits::default()
    };
    let r = Replica::new(Some(Writer::Alice), limits).unwrap();
    let (r, _) = edit(r, 0, "Friday!", vec![]);
    let delete = r.observe().unwrap()[..6]
        .iter()
        .map(|(id, _)| *id)
        .collect();
    let before = r.clone();
    let (r, result) = r.edit(0, scalars("Monday"), delete);
    assert_eq!(result, Err(Error::Capacity(Capacity::OrderingLinks)));
    assert_eq!(r, before);
    assert_eq!(text(&r), "Friday!");
}
#[test]
fn missing_prerequisite_and_capacity_return_unchanged_owned_state() {
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
        None,
        Limits {
            events: 0,
            ..Limits::default()
        },
    )
    .unwrap();
    let before = low.clone();
    let (low, result) = low.receive(&root);
    assert_eq!(result, Err(Error::Capacity(Capacity::Events)));
    assert_eq!(low, before);
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
        Some(Writer::Alice),
        Limits {
            events: 2,
            ..Limits::default()
        },
    )
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
