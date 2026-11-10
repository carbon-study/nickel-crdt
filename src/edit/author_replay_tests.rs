//! Runtime replay selection/order and a successful wrong-basis continuation.
use super::*;
fn id(writer: Writer, counter: u64) -> EventId {
    EventId { writer, counter }
}
fn example() -> (Vec<Fact>, Fact) {
    let a = Fact {
        id: id(Writer::Alice, 1),
        after: vec![],
        insert: vec!['a' as u32, 'c' as u32],
        delete: vec![],
        gap: Some(0),
    };
    let deletion = Fact {
        id: id(Writer::Bo, 1),
        after: vec![a.id],
        insert: vec![],
        delete: vec![BirthId {
            event: a.id,
            index: 0,
        }],
        gap: None,
    };
    let event = Fact {
        id: id(Writer::Alice, 2),
        after: vec![a.id],
        insert: vec!['b' as u32],
        delete: vec![],
        gap: Some(1),
    };
    (vec![a, deletion, event.clone()], event)
}
// The placement witness is authored through the public API on two receivers.
fn public_example() -> (Vec<Fact>, Fact) {
    let alice = Replica::new(Some(Writer::Alice), Limits::default()).unwrap();
    let (alice, first) = alice.edit(0, vec!['a' as u32, 'c' as u32], vec![]);
    let Local::Authored(a) = first.expect("public initial insertion") else {
        panic!("nonempty edit")
    };
    let bo = Replica::new(Some(Writer::Bo), Limits::default()).unwrap();
    let (bo, admitted) = bo.receive(&a);
    assert_eq!(admitted, Ok(Admission::Added));
    let (_, deleting) = bo.edit(
        0,
        vec![],
        vec![BirthId {
            event: a.id,
            index: 0,
        }],
    );
    let Local::Authored(deletion) = deleting.expect("public deletion") else {
        panic!("nonempty delete")
    };
    let (_, inserting) = alice.edit(1, vec!['b' as u32], vec![]);
    let Local::Authored(event) = inserting.expect("concurrent public insertion") else {
        panic!("nonempty insert")
    };
    assert_eq!(deletion.after, vec![a.id]);
    assert_eq!(event.after, vec![a.id]);
    (vec![a, deletion, event.clone()], event)
}
// Flatten first, independently of the runtime's nested group/node loops.
fn reference(operations: &[(EventId, Vec<Node>)], selected: &[EventId]) -> Result<Tree, Error> {
    let flattened: Vec<_> = operations
        .iter()
        .filter(|(id, _)| selected.contains(id))
        .flat_map(|(_, nodes)| nodes.iter().cloned())
        .collect();
    let mut tree = Tree::default();
    for node in flattened {
        tree.add(node)?;
    }
    Ok(tree)
}
#[test]
fn author_replay_filters_groups_and_keeps_node_order_and_errors() {
    let (facts, _) = example();
    let (_, nodes) = interpret_event(&facts, &facts[0], &[], Tree::default()).unwrap();
    assert_eq!(nodes.len(), 2);
    let mut duplicated = nodes.clone();
    duplicated.push(nodes[0].clone());
    let operations = vec![
        (facts[0].id, nodes.clone()),
        (facts[1].id, vec![]),
        (facts[2].id, duplicated),
    ];
    let mut success = 0;
    let mut error = 0;
    for mask in 0..8 {
        let mut selected: Vec<_> = (0..3)
            .filter(|i| mask & (1 << i) != 0)
            .map(|i| facts[i].id)
            .collect();
        selected.extend(selected.clone());
        let actual = replay_author(&operations, &selected);
        let expected = reference(&operations, &selected);
        assert_eq!(actual, expected);
        if actual.is_ok() {
            success += 1;
        } else {
            error += 1;
        }
    }
    assert_eq!((success, error), (4, 4));
    assert_eq!(
        replay_nodes(Tree::default(), &nodes),
        reference(&operations[..1], &[facts[0].id])
    );
    assert_eq!(
        replay_nodes(Tree::default(), &[nodes[0].clone(), nodes[0].clone()]),
        Err(Error::Internal)
    );
}
#[test]
fn concurrent_deletion_basis_changes_placements_without_causing_an_error() {
    let (facts, event) = public_example();
    let (tree_a, nodes_a) = interpret_event(&facts, &facts[0], &[], Tree::default()).unwrap();
    let operations = vec![(facts[0].id, nodes_a)];
    let (_, actual) = interpret_event(&facts, &event, &operations, tree_a.clone())
        .expect("correct runtime basis fits");
    let selected = past(&facts, &event.after).unwrap();
    let author = reference(&operations, &selected).unwrap();
    let correct_basis: Vec<_> = facts
        .iter()
        .filter(|f| selected.contains(&f.id))
        .cloned()
        .collect();
    let mut expected_author = author.clone();
    let expected = expected_author
        .insert(
            BirthId {
                event: event.id,
                index: 0,
            },
            'b' as u32,
            &visible(&correct_basis).unwrap(),
            1,
        )
        .unwrap();
    // Add only the unseen deletion: no future insertion/birth can make this
    // fail before the placement comparison. Both wrong and correct calls fit.
    let mut wrong_basis = correct_basis;
    wrong_basis.push(facts[1].clone());
    let mut wrong_author = author;
    let wrong = wrong_author
        .insert(
            BirthId {
                event: event.id,
                index: 0,
            },
            'b' as u32,
            &visible(&wrong_basis).unwrap(),
            1,
        )
        .expect("wrong basis still interprets successfully");
    let mut wrong_result = tree_a;
    wrong_result
        .add(wrong.clone())
        .expect("wrong operation also installs successfully");
    assert_ne!(
        expected, wrong,
        "this continuation actually separates placements"
    );
    assert_eq!(
        actual,
        vec![expected],
        "actual interpreter must exclude the unseen deletion"
    );
    assert_ne!(actual, vec![wrong]);
}
