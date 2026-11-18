use super::*;
fn quadratic(xs: &[BirthId]) -> bool {
    for i in 0..xs.len() { for j in 0..i { if xs[i] == xs[j] { return true; } } }
    false
}
fn id(n: usize) -> BirthId {
    BirthId { event: EventId { writer: if n % 2 == 0 { Writer(1) } else { Writer(2) }, counter: (n / 6) as u64 }, index: (n / 2) % 3 }
}
fn check(xs: &[BirthId]) {
    let before = xs.to_vec();
    let mut expected = xs.to_vec(); expected.sort_unstable();
    assert_eq!(ordered_births(xs), expected, "sorted scratch must retain every identity");
    assert_eq!(duplicate_births(xs), quadratic(xs), "exact duplicate decision");
    assert_eq!(xs, before, "original list is untouched");
}
#[test]
fn all_small_identity_lists_match_independent_sort_and_pairwise_oracles() {
    // Each adjacent alphabet pair differs only in writer identity.
    for n in [0, 2, 4] {
        assert_ne!(id(n).event.writer, id(n + 1).event.writer);
        assert_eq!(id(n).event.counter, id(n + 1).event.counter);
        assert_eq!(id(n).index, id(n + 1).index);
    }
    for len in 0..=6 {
        for mut code in 0..6usize.pow(len as u32) {
            let mut xs = Vec::new();
            for _ in 0..len { xs.push(id(code % 6)); code /= 6; }
            check(&xs);
        }
    }
}
#[test]
fn heap_boundaries_extreme_identities_and_nonadjacent_duplicates() {
    for len in [0,1,2,3,4,5,7,8,9,15,16,17,31,32,33,63,64,65,127,128,129,1023] {
        let mut xs: Vec<_> = (0..len).map(id).collect();
        check(&xs); xs.reverse(); check(&xs);
        if len > 1 { xs[len-1]=xs[0]; check(&xs); }
    }
    check(&[
        BirthId {event:EventId {writer:Writer(2),counter:u64::MAX},index:usize::MAX},
        BirthId {event:EventId {writer:Writer(1),counter:u64::MAX},index:usize::MAX},
        BirthId {event:EventId {writer:Writer(2),counter:0},index:0},
        BirthId {event:EventId {writer:Writer(2),counter:u64::MAX},index:0},
    ]);
}
#[test]
fn deterministic_scrambles_match_pairwise_oracle() {
    let mut seed=0x62c2_4b68_578b_d487u64;
    for len in 0..256 {
        let mut xs=Vec::new();
        for _ in 0..len { seed=seed.wrapping_mul(6364136223846793005).wrapping_add(1); xs.push(id((seed>>32) as usize % 1024)); }
        check(&xs);
    }
}
#[test]
#[ignore = "explicit release-only measurement, no timing assertion"]
fn measure_duplicate_scaling() {
    use std::{hint::black_box,time::Instant};
    for len in [64,256,1024,4096,16384] {
        for kind in ["distinct","first-pair-duplicate","near-early-duplicate","late-duplicate"] {
            let mut xs:Vec<_>=(0..len).map(id).collect();
            if kind=="first-pair-duplicate" {xs[1]=xs[0];}
            if kind=="near-early-duplicate" {xs[2]=xs[0];}
            if kind=="late-duplicate" {xs[len-1]=xs[0];}
            assert_eq!(duplicate_births(&xs),quadratic(&xs));
            let mut old=Vec::new();let mut new=Vec::new();
            for _ in 0..7 {
                let t=Instant::now();black_box(quadratic(black_box(&xs)));old.push(t.elapsed().as_nanos());
                let t=Instant::now();black_box(duplicate_births(black_box(&xs)));new.push(t.elapsed().as_nanos());
            }
            old.sort();new.sort();
            println!("duplicate-bench n={len} kind={kind} baseline_ns={} heap_ns={} ratio={:.3}",old[3],new[3],old[3] as f64/new[3] as f64);
        }
    }
}
