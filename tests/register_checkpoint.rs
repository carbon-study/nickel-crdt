// External crate boundary: no private implementation helpers or test model state.
use nickel_crdt::causal::Id;
use nickel_crdt::register::{Admission, Error, Fact, Replica, Write};
use std::collections::{BTreeMap, BTreeSet};

fn replica(writer: u64) -> Replica { Replica::new(writer, vec![0]).unwrap() }
fn snapshot(r: &Replica) -> String { format!("{r:?}") }

// Independent meaning: close the parent relation by set union, discard writes
// causally dominated at this key, then choose a maximal (Lamport, writer).
// The native winner scan does not compute this relation.
fn meaning(facts: &[Fact], key: u64) -> Vec<u8> {
    let mut past: BTreeMap<Id, BTreeSet<Id>> = facts.iter()
        .map(|f| (f.id, f.after.iter().copied().collect())).collect();
    loop {
        let old = past.clone();
        for ids in past.values_mut() {
            for id in ids.clone() { ids.extend(old[&id].iter().copied()); }
        }
        if past == old { break; }
    }
    let matching: Vec<_> = facts.iter().filter(|f| f.payload.key == key).collect();
    let maximal: Vec<_> = matching.iter().copied().filter(|f|
        !matching.iter().any(|g| past[&g.id].contains(&f.id))).collect();
    maximal.into_iter().max_by_key(|f| (f.payload.lamport, f.id.peer))
        .map_or(vec![0], |f| f.payload.value.clone())
}

#[test]
fn concurrent_winners_losers_noedit_and_independent_keys() {
    let mut a = replica(10);
    let mut b = replica(20);
    let red = a.write(7, vec![1]).unwrap().unwrap();
    let blue = b.write(7, vec![2]).unwrap().unwrap();
    assert_eq!(a.receive(blue.clone()), Ok(Admission::Added));
    assert_eq!(b.receive(red.clone()), Ok(Admission::Added));
    assert_eq!(a.read(7), vec![2]);
    assert_eq!(b.read(7), vec![2]);
    assert_eq!(a.facts().len(), 2); // losing red retained
    let before = snapshot(&a);
    assert!(a.write(7, vec![2]).unwrap().is_none());
    assert_eq!(snapshot(&a), before);
    assert_eq!(a.read(8), vec![0]);
    let other = a.write(8, vec![9]).unwrap().unwrap();
    assert_eq!(other.payload.lamport, 2);
    assert_eq!(a.read(7), vec![2]);
    let overwrite = a.write(7, vec![3]).unwrap().unwrap();
    assert_eq!(overwrite.payload.lamport, 3);
    assert_eq!(overwrite.payload.observed, vec![2]);
    b.receive(other).unwrap();
    b.receive(overwrite).unwrap();
    assert_eq!(a.read(7), vec![3]);
    assert_eq!(a.facts().len(), b.facts().len());
    assert_eq!(a.read(7), meaning(a.facts(), 7));
}

#[test]
fn author_basis_not_receiver_contamination() {
    let mut a = replica(1);
    let mut b = replica(2);
    let red = a.write(5, vec![1]).unwrap().unwrap();
    let blue = b.write(5, vec![2]).unwrap().unwrap();
    // a has a local, concurrent value, but b authored from initial black.
    assert_eq!(a.receive(blue), Ok(Admission::Added));
    assert_eq!(a.read(5), vec![2]);
    assert_eq!(a.facts().len(), 2);
    let mut c = replica(3);
    c.receive(red).unwrap();
    let same = c.write(5, vec![1]).unwrap();
    assert!(same.is_none());
    assert_eq!(c.next_counter(), 1);
}

#[test]
fn rejection_and_duplicate_preserve_full_snapshot() {
    let mut a = replica(1);
    let root = a.write(4, vec![1]).unwrap().unwrap();
    let mut r = replica(2);
    r.receive(root.clone()).unwrap();
    let before = snapshot(&r);
    assert_eq!(r.receive(root.clone()), Ok(Admission::Duplicate));
    assert_eq!(snapshot(&r), before);
    let mut conflict = root.clone(); conflict.payload.value = vec![8];
    assert_eq!(r.receive(conflict), Err(Error::Conflict));
    assert_eq!(snapshot(&r), before);
    let offered = Fact {
        id: Id { peer: 3, counter: 1 }, after: vec![root.id],
        payload: Write { key: 4, value: vec![2], observed: vec![1], lamport: 2 },
    };
    for bad in 0..8 {
        let mut f = offered.clone();
        match bad {
            0 => f.payload.observed = vec![0],
            1 => f.payload.lamport = 1,
            2 => f.payload.value = f.payload.observed.clone(),
            3 => f.id.counter = 0,
            4 => f.after.push(root.id),
            5 => f.after = vec![Id { peer: 99, counter: 1 }],
            6 => f.id.counter = 2, // producer c1 absent from author basis
            _ => f.payload.value = f.payload.observed.clone(),
        }
        assert!(r.receive(f).is_err(), "bad case {bad}");
        assert_eq!(snapshot(&r), before, "bad case {bad}");
    }
    assert_eq!(r.receive(offered), Ok(Admission::Added));
    assert_eq!(r.next_counter(), 1); // receiving isn't counter restoration
}

#[test]
fn opaque_bytes_have_no_engine_policy_budget() {
    let mut a = Replica::new(1, vec![0]).unwrap();
    let f = a.write(123, vec![255, 0, 128, 42]).unwrap().unwrap();
    let before = snapshot(&a);
    assert_eq!(a.receive(f), Ok(Admission::Duplicate)); // even full
    assert_eq!(snapshot(&a), before);
    assert!(a.write(123, vec![255, 0, 128, 42]).unwrap().is_none()); // no edit even full
    assert_eq!(snapshot(&a), before);
    assert!(a.write(456, vec![1]).unwrap().is_some());
    assert!(Replica::new(2, vec![0; 4097]).is_ok());
}

// Exercise every dependency-respecting delivery of a six-event history,
// including storage writer-order opposite the causal order.
#[test]
fn every_valid_delivery_matches_independent_causal_maxima() {
    let mut a = replica(90);
    let mut b = replica(10);
    let mut c = replica(50);
    let a1 = a.write(1, vec![1]).unwrap().unwrap();
    let b1 = b.write(1, vec![2]).unwrap().unwrap();
    c.receive(a1.clone()).unwrap();
    let c1 = c.write(2, vec![3]).unwrap().unwrap();
    a.receive(b1.clone()).unwrap();
    let a2 = a.write(1, vec![4]).unwrap().unwrap();
    b.receive(c1.clone()).unwrap_err(); // dependencies must arrive first
    b.receive(a1.clone()).unwrap();
    b.receive(c1.clone()).unwrap();
    let b2 = b.write(1, vec![5]).unwrap().unwrap();
    c.receive(b1.clone()).unwrap();
    c.receive(a2.clone()).unwrap();
    c.receive(b2.clone()).unwrap();
    let c2 = c.write(2, vec![6]).unwrap().unwrap();
    let facts = vec![a1, b1, c1, a2, b2, c2];
    fn walk(facts: &[Fact], r: Replica, seen: BTreeSet<Id>, count: &mut usize) {
        let mut expected: Vec<_> = facts.iter().filter(|f| seen.contains(&f.id)).cloned().collect();
        expected.sort_by_key(|f| f.id);
        assert_eq!(format!("{:?}", r.facts()), format!("{expected:?}"));
        for key in 0..4 { assert_eq!(r.read(key), meaning(&expected, key)); }
        if seen.len() == facts.len() {
            *count += 1;
            assert_eq!(r.read(1), vec![5]);
            assert_eq!(r.read(2), vec![6]);
            return;
        }
        for f in facts {
            if !seen.contains(&f.id) && f.after.iter().all(|id| seen.contains(id)) {
                let mut next = r.clone();
                assert_eq!(next.receive(f.clone()), Ok(Admission::Added));
                assert_eq!(next.receive(f.clone()), Ok(Admission::Duplicate));
                let mut more = seen.clone(); more.insert(f.id);
                walk(facts, next, more, count);
            }
        }
    }
    let mut count = 0; walk(&facts, replica(700), BTreeSet::new(), &mut count);
    assert!(count > 1);
}

#[test]
fn logical_clock_scans_every_key_and_reports_exact_overflow() {
    use nickel_crdt::register::next_lamport;
    let with_clock = |peer, key, lamport| Fact {
        id: Id { peer, counter: 1 }, after: vec![],
        payload: Write { key, value: vec![1], observed: vec![0], lamport },
    };
    assert_eq!(next_lamport(&[]), Ok(1));
    let facts = [with_clock(1, 7, 2), with_clock(2, 99, 20), with_clock(3, 7, 4)];
    assert_eq!(next_lamport(&facts), Ok(21));
    assert_eq!(next_lamport(&[facts[2].clone(), facts[0].clone(), facts[1].clone()]), Ok(21));
    assert_eq!(next_lamport(&[with_clock(1, 7, u64::MAX - 1)]), Ok(u64::MAX));
    assert_eq!(next_lamport(&[with_clock(1, 7, u64::MAX)]), Err(Error::ClockExhausted));
}

// All-return safety includes a rejected local write, independently of harness
// budgets. Reusing a writer is deliberately invalid, not a recovery API.
#[test]
fn failed_write_keeps_full_snapshot() {
    let mut previous_session = Replica::new(7, vec![0]).unwrap();
    let fact = previous_session.write(1, vec![1]).unwrap().unwrap();
    let mut restarted = Replica::new(7, vec![0]).unwrap();
    restarted.receive(fact).unwrap();
    let before = snapshot(&restarted);
    assert!(matches!(restarted.write(1, vec![2]), Err(Error::Conflict)));
    assert_eq!(snapshot(&restarted), before);
}
