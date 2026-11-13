//! Retained negative policy witness in the caller harness, not the Rust engine.
//! Same offered facts can leave different accepted subsets at an aggregate cap.
//! Policy changes must explicitly replace this limitation/contract, not present
//! these passing witness assertions as proof that general convergence is fixed.
use nickel_crdt::edit::*;
mod support;
use support::{Limits, Capacity, HarnessError};

fn text(replica: &Replica) -> String {
    replica
        .observe()
        .unwrap()
        .iter()
        .map(|(_, s)| char::from_u32(*s).unwrap())
        .collect()
}
fn author(replica: Replica, gap: usize, ch: char) -> (Replica, Fact) {
    let (next, result) = replica.edit(gap, vec![ch as u32], vec![]);
    let Local::Authored(fact) = result.unwrap() else {
        panic!("nonempty edit")
    };
    (next, fact)
}
fn admit(replica: Replica, fact: &Fact) -> Replica {
    let (next, result) = replica.receive(fact);
    assert_eq!(result, Ok(Admission::Added));
    next
}
fn facts() -> [Fact; 3] {
    let a = Replica::new(Some(Writer(1))).unwrap();
    let (a, root) = author(a, 0, 'x');
    let b = admit(Replica::new(Some(Writer(2))).unwrap(), &root);
    let (_, y) = author(a, 1, 'y');
    let (_, z) = author(b, 1, 'z');
    assert_eq!(y.after, vec![root.id]);
    assert_eq!(z.after, vec![root.id]);
    [root, y, z]
}
fn limited_branch(limits: Limits, order: [&Fact; 3], error: Capacity) -> Replica {
    let receiver = admit(Replica::new(None).unwrap(), order[0]);
    let receiver = admit(receiver, order[1]);
    let before = receiver.clone();
    let (receiver, result) = support::receive(receiver, order[2], limits);
    assert_eq!(result, Err(HarnessError::Budget(error)));
    assert_eq!(receiver, before, "capacity preserves the whole instance");
    // Retaining the immutable fact is necessary, but retry is not progress at
    // an unchanged full aggregate limit. This borrowed fact is never dropped.
    let (receiver, result) = support::receive(receiver, order[2], limits);
    assert_eq!(result, Err(HarnessError::Budget(error)));
    assert_eq!(receiver, before);
    let (receiver, result) = receiver.receive(order[1]);
    assert_eq!(result, Ok(Admission::Duplicate));
    assert_eq!(receiver, before, "full-state duplicate is still neutral");
    receiver
}
fn witness(small: Limits, error: Capacity) {
    let [root, y, z] = facts();
    let left = limited_branch(small, [&root, &y, &z], error);
    let right = limited_branch(small, [&root, &z, &y], error);
    assert_eq!(text(&left), "xy");
    assert_eq!(text(&right), "xz");
    assert_ne!(
        left.facts(),
        right.facts(),
        "offered set is equal, accepted sets differ"
    );
    assert_ne!(left.observe(), right.observe());
    println!("{error:?}: same three offered facts -> accepted texts xy / xz; unchanged caller-budget retry remains refused");

    // A separate, fitting-history control: reconstruct read-only observers
    // without a harness budget from ALL caller-retained offers.
    // This is not allocator recovery, an implemented promotion API, or a
    // general synchronization policy. Accepted facts alone would miss the other branch.
    let mut a = Replica::new(None).unwrap();
    let mut b = Replica::new(None).unwrap();
    for fact in [&root, &y, &z] {
        a = admit(a, fact);
    }
    for fact in [&root, &z, &y] {
        b = admit(b, fact);
    }
    assert_eq!(
        a, b,
        "complete fitting set gives exact same observer state in this witness"
    );
    assert_eq!(text(&a), "xyz");
    assert_eq!(a.facts().len(), 3);
}
#[test]
fn event_capacity_negative_witness_and_fitting_history_control() {
    witness(
        Limits {
            events: 2,
            ..Limits::default()
        },
        Capacity::Events,
    );
}
#[test]
fn retained_birth_capacity_negative_witness_and_fitting_history_control() {
    witness(
        Limits {
            births: 2,
            ..Limits::default()
        },
        Capacity::Births,
    );
}
#[test]
fn ordering_link_capacity_negative_witness_and_fitting_history_control() {
    witness(
        Limits {
            ordering_links: 6,
            ..Limits::default()
        },
        Capacity::OrderingLinks,
    );
}

#[test]
fn harness_budget_precedes_missing_but_engine_admission_is_unchanged() {
    let r = Replica::new(None).unwrap();
    let before = r.clone();
    let fact = Fact {
        id: EventId { writer: Writer(1), counter: 1 },
        after: vec![EventId { writer: Writer(2), counter: 1 }],
        insert: vec![u32::from('x'); 65], delete: vec![], gap: Some(0),
    };
    let (r, result) = support::receive(r, &fact, Limits::default());
    assert_eq!(result, Err(HarnessError::Budget(Capacity::Scalars)));
    assert_eq!(r, before);
    let (r, result) = r.receive(&fact);
    assert_eq!(result, Err(Error::Missing));
    assert_eq!(r, before);
}
