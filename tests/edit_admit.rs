use nickel_crdt::edit::*;
fn new(writer: Option<Writer>) -> Replica {
    Replica::new(writer, Limits::default()).unwrap()
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
    let (r, result) = r.edit(gap, scalars(s), delete);
    let Local::Authored(f) = result.unwrap() else {
        panic!("unexpected empty")
    };
    (r, f)
}
fn receive(r: Replica, f: &Fact) -> Replica {
    let (r, result) = r.receive(f);
    assert_eq!(result, Ok(Admission::Added));
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
    for (gap, inserted, remove_index) in [
        (0, "abc", None),
        (2, "X😀", Some(1)),
        (0, "", Some(0)),
        (3, "Z", None),
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
