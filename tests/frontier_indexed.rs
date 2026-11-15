//! Exhaustive small-graph semantics and callback-trace preservation for frontier.
//! The reference below is the pre-indexed frontier loop, not a second engine.
use nickel_crdt::event_layer::{self, GraphOps};
use std::cell::RefCell;
#[derive(Clone, Debug, PartialEq, Eq)]
struct Fact { id: u64, after: Vec<u64> }
thread_local! { static TRACE: RefCell<Vec<(u8, u64, u64)>> = const { RefCell::new(Vec::new()) }; }
fn record(k: u8, a: u64, b: u64) { TRACE.with(|t| t.borrow_mut().push((k, a, b))); }
fn id(f: &Fact) -> u64 { record(0, f.id, 0); f.id }
fn after(f: &Fact) -> &[u64] { record(1, f.id, 0); &f.after }
fn eq(a: &u64, b: &u64) -> bool { record(2, *a, *b); a == b }
fn lt(a: &u64, b: &u64) -> bool { record(3, *a, *b); a < b }
fn copy(f: &Fact) -> Fact { record(4, f.id, 0); f.clone() }
fn same(a: &Fact, b: &Fact) -> bool { record(5, a.id, b.id); a == b }
fn internal() { record(6, 0, 0); }
fn missing() { record(7, 0, 0); }
const OPS: GraphOps<Fact, u64, ()> = ((id, after, eq, lt, copy, same), (internal, missing));
fn old_frontier(facts: &[Fact]) -> Result<Vec<u64>, ()> {
    let ((id, after, _, _, _, _), (internal, _)) = OPS;
    let mut out = Vec::new();
    for f in facts {
        let mut child = false;
        for e in facts {
            if event_layer::has_id(after(e), &id(f), &OPS) { child = true; }
        }
        if !child { event_layer::push(&mut out, id(f), internal)?; }
    }
    Ok(out)
}
fn trace() -> Vec<(u8, u64, u64)> { TRACE.with(|t| std::mem::take(&mut *t.borrow_mut())) }
#[test]
fn frontier_matches_nonparents_and_preserves_callback_order() {
    let mut cases = 0;
    for n in 0..=4 {
        for repeated in [false, true] {
            for sentinel in [false, true] {
            for mask in 0u32..(1u32 << (n*n)) {
                let ids: Vec<u64> = (0..n).map(|j| if repeated { (j%2) as u64 } else { (n-j) as u64 }).collect();
                let facts: Vec<Fact> = (0..n).map(|j| {
                    let mut after: Vec<u64> = (0..n).filter(|k| mask & (1 << (j*n+k)) != 0).map(|k| ids[k]).collect();
                    if sentinel { after.push(99); } // also cover empty parent lists
                    Fact { id: ids[j], after }
                }).collect();
                let expected: Vec<u64> = ids.iter().copied().filter(|i| !facts.iter().any(|f| f.after.contains(i))).collect();
                assert!(trace().is_empty());
                let old = old_frontier(&facts); let old_trace = trace();
                let actual = event_layer::frontier(&facts, &OPS); let actual_trace = trace();
                assert_eq!(actual, Ok(expected), "n={n}, repeated={repeated}, mask={mask}");
                assert_eq!(actual, old);
                assert_eq!(actual_trace, old_trace);
                cases += 1;
            }
        }
    }
        }
    assert_eq!(cases, 264268);
}
