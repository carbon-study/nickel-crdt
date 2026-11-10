//! Native acceptance evidence for continuation §2, not its universal proof.
use super::*;
use std::collections::BTreeSet;

// Deliberately unlike past's repeated full scans: visit each reachable vertex
// once, using a worklist and an ordered set, without calling has_event/ready.
fn closure(facts: &[Fact], roots: &[EventId]) -> BTreeSet<EventId> {
    let mut todo = roots.to_vec();
    let mut seen = BTreeSet::new();
    while let Some(id) = todo.pop() {
        if seen.insert(id) {
            let fact = facts.iter().find(|f| f.id == id).expect("closed graph");
            todo.extend_from_slice(&fact.after);
        }
    }
    seen
}
fn id(i: usize) -> EventId {
    EventId {
        writer: if i % 2 == 0 {
            Writer::Alice
        } else {
            Writer::Bo
        },
        counter: (i / 2 + 1) as u64,
    }
}
fn permutations<T: Clone>(xs: &mut [T], start: usize, visit: &mut impl FnMut(&[T])) {
    if start == xs.len() {
        visit(xs);
        return;
    }
    for j in start..xs.len() {
        xs.swap(start, j);
        permutations(xs, start + 1, visit);
        xs.swap(start, j);
    }
}
#[test]
fn exact_past_on_all_four_vertex_dags_and_storage_permutations() {
    // Every edge goes from the larger topological label to the smaller one.
    // Event-ID order deliberately differs from those labels. This covers all
    // DAG shapes on <=4 vertices with this labeling, not all possible histories.
    let mut cases = 0;
    for n in 0usize..=4 {
        for edges in 0usize..(1 << (n * n.saturating_sub(1) / 2)) {
            let mut bit = 0;
            let mut facts = Vec::new();
            for i in 0..n {
                let mut after = Vec::new();
                for j in 0..i {
                    if edges & (1 << bit) != 0 {
                        after.push(id(j));
                    }
                    bit += 1;
                }
                facts.push(Fact {
                    id: id(i),
                    after,
                    insert: vec![],
                    delete: vec![],
                    gap: None,
                });
            }
            permutations(&mut facts, 0, &mut |stored| {
                for mask in 0usize..(1 << n) {
                    let roots: Vec<_> = (0..n).filter(|i| mask & (1 << i) != 0).map(id).collect();
                    let expected_choice = stored.iter().position(|fact| {
                        !roots.contains(&fact.id) && fact.after.iter().all(|id| roots.contains(id))
                    });
                    assert_eq!(choose_ready(stored, &roots), expected_choice,
                        "first eligible event under this storage order and done set");
                    let expected = closure(stored, &roots);
                    let actual = past(stored, &roots).expect("finite closed graph fits");
                    assert_eq!(actual.iter().copied().collect::<BTreeSet<_>>(), expected);
                    assert_eq!(actual.len(), expected.len(), "duplicate selected ID");
                    cases += 1;
                }
            });
        }
    }
    // Sum 2^(n*(n-1)/2) * n! * 2^n for n=0..4.
    assert_eq!(cases, 24979);
}
#[test]
fn past_roots_missing_and_transitive_domain_boundary() {
    assert_eq!(past(&[], &[]), Ok(vec![]));
    assert_eq!(past(&[], &[id(0)]), Err(Error::Missing));
    // after need not be unique for past itself: it preserves duplicate roots.
    let a = Fact {
        id: id(0),
        after: vec![],
        insert: vec![],
        delete: vec![],
        gap: None,
    };
    assert_eq!(past(&[a], &[id(0), id(0)]), Ok(vec![id(0), id(0)]));
    // Only direct roots are validated here. Missing transitive predecessors in
    // an arbitrary, non-closed state are NOT rejected by past. Public admission
    // establishes closure separately; the exact-past domain must name it.
    let broken = Fact {
        id: id(1),
        after: vec![id(0)],
        insert: vec![],
        delete: vec![],
        gap: None,
    };
    assert_eq!(past(&[broken], &[id(1)]), Ok(vec![id(1), id(0)]));
}
#[test]
fn cyclic_closed_inputs_are_not_scheduler_progress_inputs() {
    let facts = vec![
        Fact {
            id: id(0),
            after: vec![id(1)],
            insert: vec![],
            delete: vec![],
            gap: None,
        },
        Fact {
            id: id(1),
            after: vec![id(0)],
            insert: vec![],
            delete: vec![],
            gap: None,
        },
    ];
    let selected = past(&facts, &[id(0)]).unwrap();
    assert_eq!(
        selected.iter().copied().collect::<BTreeSet<_>>(),
        closure(&facts, &[id(0)])
    );
    assert_eq!(interpret(&facts), Err(Error::Internal));
}
#[test]
fn readiness_is_exact_direct_inclusion() {
    for a in 0usize..16 {
        for d in 0usize..16 {
            let after: Vec<_> = (0..4).filter(|i| a & (1 << i) != 0).map(id).collect();
            let done: Vec<_> = (0..4).filter(|i| d & (1 << i) != 0).map(id).collect();
            assert_eq!(ready(&after, &done), a & !d == 0);
        }
    }
}
fn receive_added(r: Replica, fact: &Fact) -> Replica {
    let (next, result) = r.receive(fact);
    assert_eq!(result, Ok(Admission::Added));
    next
}
fn author(r: Replica, gap: usize, text: &str, delete: Vec<BirthId>) -> (Replica, Fact) {
    let (next, result) = r.edit(gap, text.chars().map(u32::from).collect(), delete);
    let Local::Authored(fact) = result.unwrap() else {
        panic!("empty edit")
    };
    (next, fact)
}
// Child lists also contain extra concurrent events. Compare the placement that
// author reconstruction freezes, not those receiver-dependent adjacency lists.
fn placements(
    tree: &Tree,
    event: EventId,
) -> Vec<(
    BirthId,
    u32,
    Option<BirthId>,
    Option<BirthId>,
    Option<BirthId>,
    Side,
)> {
    tree.nodes
        .iter()
        .filter(|n| n.id.event == event)
        .map(|n| {
            (
                n.id,
                n.scalar,
                n.left_origin,
                n.right_origin,
                n.parent,
                n.side,
            )
        })
        .collect()
}
#[test]
fn receiver_extras_preserve_exact_author_placements_through_public_admission() {
    let new = |w| Replica::new(w, Limits::default()).unwrap();
    let (a, root) = author(new(Some(Writer::Alice)), 0, "ab", vec![]);
    let b = receive_added(new(Some(Writer::Bo)), &root);
    let a_victim = a.observe().unwrap()[0].0;
    let (a, replacement) = author(a, 0, "X", vec![a_victim]);
    let (b, sibling) = author(b, 0, "Y", vec![]);
    let a = receive_added(a, &sibling);
    let b = receive_added(b, &replacement);
    let b_victim = a
        .observe()
        .unwrap()
        .iter()
        .find(|(_, s)| *s == u32::from('b'))
        .unwrap()
        .0;
    let (a, second) = author(a, 1, "Q", vec![b_victim]);
    let (b, prepend) = author(b, 0, "Z", vec![]);
    let a = receive_added(a, &prepend);
    let (_a, join) = author(a, 0, "!", vec![]);
    let _b = b;
    let facts = vec![root, replacement, sibling, second, prepend, join];
    // The oracle basis is graph closure, not past. The comparison is native
    // reconstruction locality, not an independent FugueMax semantics oracle.
    let mut expected = Vec::new();
    for f in &facts {
        let ancestors = closure(&facts, &f.after);
        let mut basis: Vec<_> = facts
            .iter()
            .filter(|g| ancestors.contains(&g.id))
            .cloned()
            .collect();
        basis.push(f.clone());
        basis.sort_by_key(|g| g.id);
        expected.push((f.id, placements(&interpret(&basis).unwrap(), f.id)));
    }
    let mut delivered = 0;
    let mut orders = facts.clone();
    permutations(&mut orders, 0, &mut |order| {
        let mut seen = BTreeSet::new();
        if !order.iter().all(|f| {
            if !f.after.iter().all(|id| seen.contains(id)) {
                return false;
            }
            seen.insert(f.id);
            true
        }) {
            return;
        }
        let mut r = new(None);
        for f in order {
            r = receive_added(r, f);
            for (id, wanted) in &expected {
                if seen_in(r.facts(), *id) {
                    assert_eq!(
                        placements(&r.tree, *id),
                        *wanted,
                        "author basis changed with receiver extras"
                    );
                }
            }
        }
        assert_eq!(r.facts().len(), facts.len());
        assert_eq!(r.tree, interpret(r.facts()).unwrap());
        delivered += 1;
    });
    assert_eq!(delivered, 4, "all legal causal schedules of this fixture");
}
fn seen_in(facts: &[Fact], id: EventId) -> bool {
    facts.iter().any(|f| f.id == id)
}
