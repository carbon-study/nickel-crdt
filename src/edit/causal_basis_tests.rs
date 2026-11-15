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
    let new = |w| Replica::new(w).unwrap();
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

// Frozen pre-refactor implementation: checks error values and full Tree, not
// just the visible text or the extracted schedule. Test-only, never extracted.
fn interpret_before_schedule_refactor(facts: &[Fact]) -> Result<Tree, Error> {
    let mut result = Tree::default();
    let mut done: Vec<EventId> = Vec::new();
    let mut operations: Vec<(EventId, Vec<Node>)> = Vec::new();
    for _ in 0..facts.len() {
        let index = choose_ready(facts, &done).ok_or(Error::Internal)?;
        if index >= facts.len() {
            return Err(Error::Internal);
        }
        let event = &facts[index];
        let selected = past(facts, &event.after)?;
        let mut basis = Vec::new();
        for f in facts {
            if has_event(&selected, f.id) {
                push(&mut basis, f.clone())?;
            }
        }
        let mut author = Tree::default();
        for i in 0..operations.len() {
            let pair: (EventId, Vec<Node>) = operations[i].clone();
            let (id, ops) = pair;
            if has_event(&selected, id) {
                for j in 0..ops.len() {
                    author.add(ops[j].clone())?;
                }
            }
        }
        let mut seen = visible(&basis)?;
        let mut ops = Vec::new();
        if !event.insert.is_empty() {
            let gap = event.gap.ok_or(Error::Internal)?;
            for index in 0..event.insert.len() {
                let id = BirthId {
                    event: event.id,
                    index,
                };
                let op = author.insert(id, event.insert[index], &seen, add(gap, index)?)?;
                push(&mut ops, op)?;
                push(&mut seen, id)?;
            }
        }
        for i in 0..ops.len() {
            result.add(ops[i].clone())?;
        }
        push(&mut done, event.id)?;
        push(&mut operations, (event.id, ops))?;
    }
    Ok(result)
}

fn assert_complete_causal_trace(stored: &[Fact], trace: &[EventId]) {
    let mut seen = BTreeSet::new();
    for &event in trace {
        let fact = stored
            .iter()
            .find(|fact| fact.id == event)
            .expect("stored event");
        assert!(
            fact.after.iter().all(|id| seen.contains(id)),
            "predecessor not yet run"
        );
        // Independent oracle chooses the least eligible storage index.
        let expected = stored
            .iter()
            .find(|f| !seen.contains(&f.id) && f.after.iter().all(|id| seen.contains(id)))
            .unwrap();
        assert_eq!(event, expected.id);
        assert!(seen.insert(event), "event ran twice");
    }
    assert_eq!(seen, stored.iter().map(|fact| fact.id).collect());
}

#[test]
fn actual_outer_schedule_is_once_only_causal_and_refactor_preserves_results() {
    let mut cases = 0;
    let mut successful_nonempty_traces = 0;
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
                let (tree, trace) =
                    interpret_scheduled(stored).expect("closed empty-effect DAG fits");
                assert_eq!(interpret(stored), Ok(tree));
                assert_eq!(
                    interpret(stored),
                    interpret_before_schedule_refactor(stored)
                );
                assert_complete_causal_trace(stored, &trace);
                // Nonempty insertions and invalid gaps exercise the moved helper's
                // success/error paths, still comparing the entire returned Tree.
                for gap in [None, Some(0), Some(1), Some(usize::MAX)] {
                    let mut changed = stored.to_vec();
                    for fact in &mut changed {
                        fact.insert = vec!['x' as u32];
                        fact.gap = gap;
                    }
                    let scheduled = interpret_scheduled(&changed);
                    if let Ok((_, trace)) = &scheduled {
                        assert_complete_causal_trace(&changed, trace);
                        if !changed.is_empty() {
                            successful_nonempty_traces += 1;
                        }
                    }
                    if !changed.is_empty() {
                        assert_eq!(scheduled.is_ok(), gap == Some(0), "nonempty gap domain");
                    }
                    assert_eq!(
                        interpret(&changed),
                        interpret_before_schedule_refactor(&changed)
                    );
                }
                cases += 1;
            });
        }
    }
    assert_eq!(cases, 1590);
    assert_eq!(successful_nonempty_traces, 1589);
    let nonempty = Fact {
        id: id(0),
        after: vec![],
        insert: vec!['x' as u32],
        delete: vec![],
        gap: Some(0),
    };
    let (tree, done) = interpret_scheduled(&[nonempty]).expect("one text event succeeds");
    assert_eq!(done, vec![id(0)]);
    assert_eq!(tree.nodes.len(), 1);
}

// Exercise the moved visible-basis and gap+index paths using only public
// author/admit calls, with real deletions and distinct multi-scalar inserts.
#[test]
fn authored_delete_and_multi_scalar_histories_preserve_full_interpretation() {
    fn check(replica: &Replica) {
        let (tree, trace) = interpret_scheduled(replica.facts()).expect("authored history fits");
        assert_complete_causal_trace(replica.facts(), &trace);
        assert_eq!(
            Ok(tree.clone()),
            interpret_before_schedule_refactor(replica.facts())
        );
        assert_eq!(tree, replica.tree);
    }
    let mut authored = 0;
    let mut deleting = 0;
    let mut multi_scalar = 0;
    let mut checked = 0;
    for seed in 0u64..24 {
        let mut state = seed + 1;
        let mut replicas = [
            Replica::new(Some(Writer::Alice)).unwrap(),
            Replica::new(Some(Writer::Bo)).unwrap(),
        ];
        let mut facts = Vec::new();
        for step in 0..12 {
            state = state.wrapping_mul(6364136223846793005).wrapping_add(1);
            let actor = ((state >> 32) & 1) as usize;
            let visible = replicas[actor].observe().unwrap();
            let gap = ((state >> 16) as usize) % (visible.len() + 1);
            let delete = if step % 3 == 0 && !visible.is_empty() {
                vec![visible[(state as usize) % visible.len()].0]
            } else {
                vec![]
            };
            let count = 1 + (step + seed as usize) % 3;
            let insert = ['A' as u32, 'ß' as u32, '🦀' as u32][..count].to_vec();
            let (next, result) = replicas[actor].clone().edit(gap, insert, delete);
            let Local::Authored(fact) = result.expect("bounded public edit") else {
                panic!("nonempty edit")
            };
            authored += 1;
            deleting += usize::from(!fact.delete.is_empty());
            multi_scalar += usize::from(fact.insert.len() > 1);
            facts.push(fact);
            replicas[actor] = next;
            check(&replicas[actor]);
            checked += 1;
            if step % 2 == 1 {
                for replica in &mut replicas {
                    for fact in &facts {
                        let (next, outcome) = replica.clone().receive(fact);
                        assert!(matches!(
                            outcome,
                            Ok(Admission::Added | Admission::Duplicate)
                        ));
                        *replica = next;
                    }
                    check(replica);
                    checked += 1;
                }
            }
        }
        let mut union = Replica::new(None).unwrap();
        for fact in &facts {
            union = receive_added(union, fact);
        }
        check(&union);
        checked += 1;
    }
    assert_eq!(
        (authored, deleting, multi_scalar, checked),
        (288, 72, 192, 600)
    );
}

#[test]
fn actual_past_cut_retains_the_actual_execution_order() {
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
                    insert: vec!['a' as u32 + i as u32],
                    delete: vec![],
                    gap: Some(0),
                });
            }
            permutations(&mut facts, 0, &mut |stored| {
                let (_, done) = interpret_scheduled(stored).expect("full text DAG fits");
                assert_complete_causal_trace(stored, &done);
                for mask in 0usize..(1 << n) {
                    let roots: Vec<_> = (0..n).filter(|i| mask & (1 << i) != 0).map(id).collect();
                    assert!(!duplicate_events(&roots));
                    let independent = closure(stored, &roots);
                    let selected = past(stored, &roots).expect("closed roots");
                    assert_eq!(
                        selected.iter().copied().collect::<BTreeSet<_>>(),
                        independent
                    );
                    let projected: Vec<_> = done
                        .iter()
                        .copied()
                        .filter(|id| independent.contains(id))
                        .collect();
                    let basis: Vec<_> = stored
                        .iter()
                        .filter(|f| independent.contains(&f.id))
                        .cloned()
                        .collect();
                    assert_complete_causal_trace(&basis, &projected);
                    let (_, separately_executed) =
                        interpret_scheduled(&basis).expect("past-only text DAG fits");
                    // Stronger finite witness: the pure relative-order theorem
                    // does not yet claim equality with this separate execution.
                    assert_eq!(projected, separately_executed);
                    cases += 1;
                }
            });
        }
    }
    assert_eq!(cases, 24979);
}

// Two receivers with different concurrent extras select the same past for the
// same event. Each actual past is compared with the independent closure oracle,
// not only with the other receiver: both could otherwise share one wrong set.
// Selected IDs only; interpreted placements are the test above.
#[test]
fn two_receivers_with_different_extras_select_the_same_past() {
    let new = |w| Replica::new(w).unwrap();
    let (a, root) = author(new(Some(Writer::Alice)), 0, "ab", vec![]);
    let b = receive_added(new(Some(Writer::Bo)), &root);
    let (b, x) = author(b, 0, "x", vec![]);
    let (a, y) = author(a, 2, "y", vec![]);
    let a = receive_added(a, &x);
    let (a, e) = author(a, 1, "e", vec![]);
    // Extras: z is concurrent with y and e (Bo has not seen y); w follows e.
    let (_b, z) = author(b, 1, "z", vec![]);
    let (_a, w) = author(a, 0, "w", vec![]);
    let shared = vec![root.clone(), x.clone(), y.clone()];
    let mut all = shared.clone();
    all.extend([e.clone(), z.clone(), w.clone()]);
    let expected = closure(&all, &e.after);
    assert_eq!(expected, shared.iter().map(|f| f.id).collect::<BTreeSet<_>>(), "fixture past");
    let mut observed = BTreeSet::new();
    let mut stores = BTreeSet::new();
    // Legal causal orders after root, counted by hand: x and y in either order,
    // z needs x, w needs e. Shared only: 2; +w: 2; +z: 5; +z+w: 7.
    for (extras, legal) in [
        (vec![z.clone()], 5),
        (vec![w.clone()], 2),
        (vec![z.clone(), w.clone()], 7),
        (vec![], 2),
    ] {
        let mut delivered = 0;
        let mut facts = shared.clone();
        facts.push(e.clone());
        facts.extend(extras.iter().cloned());
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
            delivered += 1;
            let mut r = new(None);
            for f in order {
                r = receive_added(r, f);
            }
            let selected = past(r.facts(), &e.after).expect("closed receiver history fits");
            let set: BTreeSet<_> = selected.iter().copied().collect();
            assert_eq!(selected.len(), set.len(), "duplicate selected ID");
            assert_eq!(set, expected, "receiver past differs from the exact closure");
            // Contamination witness: the extras are stored here but never selected.
            for extra in &extras {
                assert!(seen_in(r.facts(), extra.id) && !set.contains(&extra.id));
            }
            observed.insert(set.into_iter().collect::<Vec<_>>());
            stores.insert(r.facts().iter().map(|f| f.id).collect::<Vec<_>>());
        });
        assert_eq!(delivered, legal, "every legal causal delivery order of this extra set");
    }
    assert_eq!(observed.len(), 1, "every receiver selected one past");
    assert_eq!(stores.len(), 4, "the receivers really stored different histories");
}

#[test]
fn outer_errors_have_a_concrete_event_work_witness() {
    let first = Fact {
        id: id(0),
        after: vec![],
        insert: vec!['x' as u32],
        delete: vec![],
        gap: Some(0),
    };
    let mut cases = 0;
    for gap in [None, Some(2), Some(usize::MAX)] {
        let bad = Fact {
            id: id(1),
            after: vec![first.id],
            insert: vec!['y' as u32],
            delete: vec![],
            gap,
        };
        let mut facts = vec![first.clone(), bad.clone()];
        permutations(&mut facts, 0, &mut |stored| {
            // This witnesses the actual failing helper call after a successful
            // first event. No public admission success is claimed for bad gaps.
            let (tree, ops) =
                interpret_event(stored, &first, &[], Tree::default()).expect("first event fits");
            let done = vec![first.id];
            let operations = vec![(first.id, ops)];
            assert_complete_causal_trace(&[first.clone()], &done);
            assert_eq!(operations.len(), done.len());
            assert!(done.len() < stored.len());
            assert!(bad.after.iter().all(|id| done.contains(id)));
            let error = interpret_event(stored, &bad, &operations, tree)
                .expect_err("bad gap fails inside event work");
            assert_eq!(interpret_scheduled(stored), Err(error.clone()));
            assert_eq!(interpret(stored), Err(error));
            cases += 1;
        });
    }
    assert_eq!(cases, 6);
}

#[test]
fn error_witness_uses_reachable_prefix_not_an_adversarial_tree() {
    // Reviewer counterexample: an empty A and inserting B. A fabricated tree
    // already containing B makes B fail, but that is not a reachable prefix.
    let a = Fact {
        id: id(0),
        after: vec![],
        insert: vec![],
        delete: vec![],
        gap: None,
    };
    let b = Fact {
        id: id(1),
        after: vec![],
        insert: vec!['b' as u32],
        delete: vec![],
        gap: Some(0),
    };
    let facts = vec![a, b.clone()];
    let (adversarial, _) = interpret_event(&facts, &b, &[], Tree::default()).unwrap();
    assert_eq!(
        interpret_event(&facts, &b, &[], adversarial.clone()),
        Err(Error::Internal)
    );
    assert_ne!(
        adversarial,
        Tree::default(),
        "zero-step prefix is the actual default tree"
    );

    // Construct every prefix along the *actual choice/helper* schedule. This
    // is independent of interpret_scheduled's bookkeeping/error branches.
    let mut done = Vec::new();
    let mut operations = Vec::new();
    let mut tree = Tree::default();
    for _ in 0..facts.len() {
        let index = choose_ready(&facts, &done).expect("ranked incomplete prefix");
        let event = &facts[index];
        let (next, ops) = interpret_event(&facts, event, &operations, tree)
            .expect("no event work fails on a reachable prefix in this history");
        tree = next;
        done.push(event.id);
        operations.push((event.id, ops));
    }
    assert_eq!(done, vec![id(0), id(1)]);
    assert_eq!(interpret_scheduled(&facts), Ok((tree.clone(), done)));
    assert_eq!(interpret(&facts), Ok(tree));
}
