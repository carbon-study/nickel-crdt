//! More than two peers: opaque u64 writers, including 0 and u64::MAX.
//! Finite native witnesses only; the universal statements are the proofs.
use nickel_crdt::edit::*;

const PEERS: [u64; 6] = [0, 1, 2, 3, 1 << 40, u64::MAX];

fn text(r: &Replica) -> String {
    r.observe().unwrap().iter().map(|(_, s)| char::from_u32(*s).unwrap()).collect()
}
fn author(r: Replica, gap: usize, s: &str) -> (Replica, Fact) {
    let (r, result) = r.edit(gap, s.chars().map(u32::from).collect(), vec![]);
    let Ok(Local::Authored(fact)) = result else { panic!("edit failed: {result:?}") };
    (r, fact)
}
fn admit(r: Replica, f: &Fact) -> Replica {
    let (r, result) = r.receive(f);
    assert_eq!(result, Ok(Admission::Added), "{f:?}");
    r
}
// Root by peer 5 (not in PEERS: a restarted writer may not reuse its stream), then every peer inserts its own letter at the end concurrently.
fn concurrent_appends() -> (Fact, Vec<Fact>) {
    let (_, root) = author(Replica::new(Some(Writer(5))).unwrap(), 0, "x");
    let mut appends = Vec::new();
    for (i, peer) in PEERS.iter().enumerate() {
        let r = admit(Replica::new(Some(Writer(*peer))).unwrap(), &root);
        let (_, f) = author(r, 1, &char::from(b'a' + i as u8).to_string());
        appends.push(f);
    }
    (root, appends)
}

#[test]
fn same_counter_on_distinct_peers_is_not_a_conflict() {
    let (root, appends) = concurrent_appends();
    let mut r = admit(Replica::new(None).unwrap(), &root);
    for f in &appends {
        r = admit(r, f);
    }
    assert_eq!(r.facts().len(), 1 + PEERS.len());
    // Canonical storage is (numeric peer, counter) order.
    let ids: Vec<EventId> = r.facts().iter().map(|f| f.id).collect();
    assert!(ids.windows(2).all(|w| w[0] < w[1]));
    assert_eq!(ids[0].writer, Writer(0));
    assert_eq!(ids.last().unwrap().writer, Writer(u64::MAX));
}

#[test]
fn every_delivery_order_of_six_peers_converges() {
    let (root, appends) = concurrent_appends();
    let mut reference: Option<(String, Vec<Fact>)> = None;
    // Deterministic sample of permutations (all 720 are cheap enough).
    let mut order: Vec<usize> = (0..appends.len()).collect();
    let mut count = 0;
    loop {
        let mut r = admit(Replica::new(None).unwrap(), &root);
        for &i in &order {
            r = admit(r, &appends[i]);
        }
        let seen = (text(&r), r.facts().to_vec());
        match &reference {
            None => reference = Some(seen),
            Some(expected) => assert_eq!(&seen, expected, "order {order:?}"),
        }
        count += 1;
        // next lexicographic permutation
        let Some(k) = (0..order.len() - 1).rev().find(|&k| order[k] < order[k + 1]) else { break };
        let l = (k + 1..order.len()).rev().find(|&l| order[k] < order[l]).unwrap();
        order.swap(k, l);
        order[k + 1..].reverse();
    }
    assert_eq!(count, 720);
    let (text, _) = reference.unwrap();
    assert_eq!(text.len(), 1 + PEERS.len());
    assert!(text.starts_with('x'));
}

#[test]
fn a_third_peer_builds_on_two_others() {
    let (a, f1) = author(Replica::new(Some(Writer(7))).unwrap(), 0, "ab");
    let b = admit(Replica::new(Some(Writer(9))).unwrap(), &f1);
    let (b, f2) = author(b, 2, "c");
    let c = admit(admit(Replica::new(Some(Writer(11))).unwrap(), &f1), &f2);
    let (_, f3) = author(c, 0, "z");
    assert_eq!(f3.after, vec![f2.id], "frontier of the third peer");
    let mut r = admit(admit(admit(Replica::new(None).unwrap(), &f1), &f2), &f3);
    assert_eq!(text(&r), "zabc");
    // The first author, catching up, reaches the same state as a fresh observer.
    let a = admit(admit(a, &f2), &f3);
    r = admit(Replica::new(None).unwrap(), &f1);
    r = admit(admit(r, &f2), &f3);
    assert_eq!(a.facts(), r.facts());
    assert_eq!(text(&a), "zabc");
}
