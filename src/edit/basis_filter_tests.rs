//! Whole-fact filter and actual interpreter integration witnesses.
use super::*;
fn id(counter: u64) -> EventId {
    EventId {
        writer: Writer(1),
        counter,
    }
}
#[test]
fn basis_filter_keeps_exact_whole_facts_and_storage_order() {
    // Include duplicate IDs with different contents: selection is by ID, but
    // the output must retain each whole fact and its original occurrence.
    let facts: Vec<Fact> = (0..4)
        .map(|i| Fact {
            id: id(i % 3 + 1),
            after: vec![id(9 + i)],
            insert: vec!['a' as u32 + i as u32, 0x1f980],
            delete: vec![BirthId {
                event: id(8),
                index: i as usize,
            }],
            gap: Some(i as usize),
        })
        .collect();
    let mut cases = 0;
    for permutation in [[0, 1, 2, 3], [3, 1, 0, 2], [2, 3, 1, 0]] {
        let input: Vec<_> = permutation.iter().map(|&i| facts[i].clone()).collect();
        for mask in 0..8 {
            let mut selected: Vec<_> = (0..3)
                .filter(|i| mask & (1 << i) != 0)
                .map(|i| id(i + 1))
                .collect();
            selected.push(id(99)); // A selected ID need not occur in facts.
            selected.extend(selected.clone()); // Duplicate selectors do not duplicate output.
            let expected: Vec<_> = input
                .iter()
                .filter(|f| selected.contains(&f.id))
                .cloned()
                .collect();
            assert_eq!(select_basis(&input, &selected), Ok(expected));
            cases += 1;
        }
    }
    assert_eq!(cases, 24);
    assert_eq!(select_basis(&[], &[id(1)]), Ok(vec![]));
}
#[test]
fn event_basis_excludes_concurrent_deletion_in_actual_interpreter() {
    let a = Fact {
        id: id(1),
        after: vec![],
        insert: vec!['a' as u32],
        delete: vec![],
        gap: Some(0),
    };
    let deleting_extra = Fact {
        id: id(2),
        after: vec![a.id],
        insert: vec![],
        delete: vec![BirthId {
            event: a.id,
            index: 0,
        }],
        gap: None,
    };
    let event = Fact {
        id: id(3),
        after: vec![a.id],
        insert: vec!['b' as u32],
        delete: vec![],
        gap: Some(1),
    };
    let full = vec![a.clone(), deleting_extra, event.clone()];
    let (tree_a, ops_a) = interpret_event(&full, &a, &[], Tree::default()).unwrap();
    let (next, ops) = interpret_event(&full, &event, &[(a.id, ops_a)], tree_a).unwrap();
    let subset = vec![a.clone(), event.clone()];
    let (subset_a, subset_ops_a) = interpret_event(&subset, &a, &[], Tree::default()).unwrap();
    let (expected, expected_ops) =
        interpret_event(&subset, &event, &[(a.id, subset_ops_a)], subset_a).unwrap();
    assert_eq!(
        ops, expected_ops,
        "concurrent deletion must not enter author's visible basis"
    );
    assert_eq!(next, expected);
}
#[test]
fn actual_event_basis_matches_independent_closure_and_fact_filter() {
    use std::collections::BTreeSet;
    let mut cases = 0;
    for edges in 0..64u32 {
        let mut bit = 0;
        let facts: Vec<_> = (0..4u64)
            .map(|i| {
                let mut after = Vec::new();
                for j in 0..i {
                    if edges & (1 << bit) != 0 {
                        after.push(id(j + 1));
                    }
                    bit += 1;
                }
                Fact {
                    id: id(i + 1),
                    after,
                    insert: vec!['a' as u32 + i as u32],
                    delete: vec![],
                    gap: Some(i as usize),
                }
            })
            .collect();
        for order in [[0, 1, 2, 3], [3, 2, 1, 0], [1, 3, 0, 2]] {
            let stored: Vec<_> = order.iter().map(|&i| facts[i].clone()).collect();
            for mask in 0..16 {
                let roots: Vec<_> = (0..4)
                    .filter(|i| mask & (1 << i) != 0)
                    .map(|i| id(i + 1))
                    .collect();
                let event = Fact {
                    id: id(99),
                    after: roots.clone(),
                    insert: vec![],
                    delete: vec![],
                    gap: None,
                };
                // Worklist oracle, independent of past's bounded repeated scans.
                let mut todo = roots;
                let mut selected = BTreeSet::new();
                while let Some(current) = todo.pop() {
                    if selected.insert(current) {
                        let fact = facts.iter().find(|f| f.id == current).unwrap();
                        todo.extend_from_slice(&fact.after);
                    }
                }
                let expected: Vec<_> = stored
                    .iter()
                    .filter(|f| selected.contains(&f.id))
                    .cloned()
                    .collect();
                let (actual_ids, actual_facts) = event_basis(&stored, &event).unwrap();
                assert_eq!(actual_ids.len(), selected.len());
                assert_eq!(actual_ids.into_iter().collect::<BTreeSet<_>>(), selected);
                assert_eq!(actual_facts, expected);
                cases += 1;
            }
        }
    }
    assert_eq!(cases, 3072);
}
