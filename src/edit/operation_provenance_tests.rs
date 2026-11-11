//! Completed execution compared with a separately driven helper replay.
//! This checks actual primitive calls, not independent FugueMax semantics.
use super::*;

fn event(writer: Writer, counter: u64) -> EventId {
    EventId { writer, counter }
}
fn permutations(facts: &mut [Fact], at: usize, visit: &mut impl FnMut(&[Fact])) {
    if at == facts.len() {
        visit(facts);
    } else {
        for next in at..facts.len() {
            facts.swap(at, next);
            permutations(facts, at + 1, visit);
            facts.swap(at, next);
        }
    }
}

#[test]
fn completed_tree_and_trace_have_all_helper_produced_groups() {
    let a = event(Writer::Alice, 1);
    let b = event(Writer::Bo, 1);
    let c = event(Writer::Alice, 2);
    let d = event(Writer::Bo, 2);
    // Literal facts keep the comparison reachable under an outer-interpreter
    // mutant: fixture authoring must not fail before the intended assertion.
    let mut facts = vec![
        Fact {
            id: a,
            after: vec![],
            insert: vec!['a' as u32, 'c' as u32],
            delete: vec![],
            gap: Some(0),
        },
        Fact {
            id: b,
            after: vec![a],
            insert: vec![],
            delete: vec![BirthId { event: a, index: 0 }],
            gap: None,
        },
        Fact {
            id: c,
            after: vec![a],
            insert: vec!['b' as u32],
            delete: vec![],
            gap: Some(1),
        },
        Fact {
            id: d,
            after: vec![b, c],
            insert: vec!['d' as u32],
            delete: vec![],
            gap: Some(1),
        },
    ];
    let mut cases = 0;
    permutations(&mut facts, 0, &mut |stored| {
        let mut done = Vec::new();
        let mut groups: Vec<(EventId, Vec<Node>)> = Vec::new();
        let mut tree = Tree::default();
        while done.len() < stored.len() {
            // Independent first-ready search; do not call choose_ready here.
            let fact = stored
                .iter()
                .find(|fact| {
                    !done.contains(&fact.id) && fact.after.iter().all(|id| done.contains(id))
                })
                .expect("this four-event DAG has a ready event");
            let (next, nodes) = interpret_event(stored, fact, &groups, tree)
                .expect("the concrete event work succeeds");
            assert_eq!(nodes.len(), fact.insert.len());
            for (index, node) in nodes.iter().enumerate() {
                assert_eq!(
                    node.id,
                    BirthId {
                        event: fact.id,
                        index
                    }
                );
                assert_eq!(node.scalar, fact.insert[index]);
            }
            done.push(fact.id);
            groups.push((fact.id, nodes));
            tree = next;
            assert_eq!(groups.iter().map(|(id, _)| *id).collect::<Vec<_>>(), done);
        }
        assert_eq!(groups.len(), 4);
        assert_eq!(
            groups.iter().filter(|(_, nodes)| nodes.is_empty()).count(),
            1
        );
        assert_eq!(
            groups.iter().map(|(_, nodes)| nodes.len()).sum::<usize>(),
            4
        );
        assert_eq!(
            tree.whole().unwrap(),
            vec![
                BirthId { event: a, index: 0 },
                BirthId { event: c, index: 0 },
                BirthId { event: d, index: 0 },
                BirthId { event: a, index: 1 },
            ]
        );
        assert_eq!(interpret_scheduled(stored), Ok((tree.clone(), done)));
        assert_eq!(interpret(stored), Ok(tree));
        cases += 1;
    });
    assert_eq!(
        cases, 24,
        "every storage permutation reaches the comparison"
    );
    assert_eq!(interpret_scheduled(&[]), Ok((Tree::default(), vec![])));
}
