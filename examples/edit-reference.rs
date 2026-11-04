//! Development fixture exporter, not a public serialization format.
use nickel_crdt::edit::*;
fn new(w: Option<Writer>) -> Replica {
    Replica::new(w, Limits::default()).unwrap()
}
fn edit(r: Replica, gap: usize, s: &str, delete: Vec<BirthId>) -> (Replica, Fact) {
    let (r, result) = r.edit(gap, s.chars().map(u32::from).collect(), delete);
    let Local::Authored(f) = result.unwrap() else {
        panic!()
    };
    (r, f)
}
fn recv(r: Replica, f: &Fact) -> Replica {
    let (r, result) = r.receive(f);
    result.unwrap();
    r
}
fn w(w: Writer) -> u8 {
    match w {
        Writer::Alice => 0,
        Writer::Bo => 1,
    }
}
fn event(id: EventId) -> String {
    format!("[{},{}]", w(id.writer), id.counter)
}
fn birth(id: BirthId) -> String {
    format!("[{},{},{}]", w(id.event.writer), id.event.counter, id.index)
}
fn fact(f: &Fact) -> String {
    format!("{{\"writer\":{},\"counter\":{},\"after\":[{}],\"insert\":{:?},\"delete\":[{}],\"gap\":{}}}",w(f.id.writer),f.id.counter,f.after.iter().map(|id|event(*id)).collect::<Vec<_>>().join(","),f.insert,f.delete.iter().map(|id|birth(*id)).collect::<Vec<_>>().join(","),f.gap.map(|x|x.to_string()).unwrap_or_else(||"null".into()))
}
fn schedules(prefix: Vec<Fact>, rest: Vec<Fact>, out: &mut Vec<Vec<Fact>>) {
    if rest.is_empty() {
        out.push(prefix);
        return;
    }
    for i in 0..rest.len() {
        if rest[i]
            .after
            .iter()
            .all(|id| prefix.iter().any(|f| f.id == *id))
        {
            let mut todo = rest.clone();
            let f = todo.remove(i);
            let mut next = prefix.clone();
            next.push(f);
            schedules(next, todo, out)
        }
    }
}
fn case(name: &str, facts: Vec<Fact>) -> String {
    let mut orders = Vec::new();
    schedules(vec![], facts.clone(), &mut orders);
    let mut observations = Vec::new();
    for order in &orders {
        let mut r = new(None);
        for f in order {
            r = recv(r, f)
        }
        observations.push((r.whole().unwrap(), r.observe().unwrap()));
    }
    assert!(observations.iter().all(|x| *x == observations[0]));
    let (whole, visible) = &observations[0];
    format!(
        "{{\"name\":\"{}\",\"facts\":[{}],\"orders\":{},\"whole\":[{}],\"visible\":[{}]}}",
        name,
        facts.iter().map(fact).collect::<Vec<_>>().join(","),
        orders.len(),
        whole
            .iter()
            .map(|id| birth(*id))
            .collect::<Vec<_>>()
            .join(","),
        visible
            .iter()
            .map(|(id, s)| format!(
                "[{},{},{},{}]",
                w(id.event.writer),
                id.event.counter,
                id.index,
                s
            ))
            .collect::<Vec<_>>()
            .join(",")
    )
}
fn main() {
    let mut cases = Vec::new();
    for prepend in [true, false] {
        let (a, root) = edit(new(Some(Writer::Alice)), 0, "ab", vec![]);
        let b = recv(new(Some(Writer::Bo)), &root);
        let (a, one) = edit(a, 1, "1", vec![]);
        let (_, two) = edit(a, if prepend { 1 } else { 2 }, "2", vec![]);
        let (b, three) = edit(b, 1, "3", vec![]);
        let (_, four) = edit(b, if prepend { 1 } else { 2 }, "4", vec![]);
        cases.push(case(
            if prepend { "prepend" } else { "append" },
            vec![root, one, two, three, four],
        ));
    }
    let (a, root) = edit(new(Some(Writer::Alice)), 0, "ab", vec![]);
    let b = recv(new(Some(Writer::Bo)), &root);
    let (_, x) = edit(a, 2, "X", vec![]);
    let id = b.observe().unwrap()[1].0;
    let (_, del) = edit(b, 0, "", vec![id]);
    cases.push(case("author-last-gap", vec![root, x, del]));
    let (a, root) = edit(new(Some(Writer::Alice)), 0, "ab", vec![]);
    let id = a.observe().unwrap()[0].0;
    let (a, del) = edit(a, 0, "", vec![id]);
    let (_, x) = edit(a, 0, "X", vec![]);
    cases.push(case("before-hidden", vec![root, del, x]));
    let (a, root) = edit(new(Some(Writer::Alice)), 0, "Friday!", vec![]);
    let b = recv(new(Some(Writer::Bo)), &root);
    let ids = b.observe().unwrap()[..6]
        .iter()
        .map(|(id, _)| *id)
        .collect();
    let (_, replace) = edit(b, 0, "Monday", ids);
    let (_, suffix) = edit(a, 7, "?", vec![]);
    cases.push(case("concurrent-replacement", vec![root, replace, suffix]));
    let (_, unicode) = edit(new(Some(Writer::Alice)), 0, "\0\r\n\u{feff}😀𝄞é", vec![]);
    cases.push(case("scalars", vec![unicode]));
    // Bounded construction: all two-step insertion gaps for two offline writers.
    for a1 in 0..=2 {
        for a2 in 0..=3 {
            for b1 in 0..=2 {
                for b2 in 0..=3 {
                    let (a, root) = edit(new(Some(Writer::Alice)), 0, "ab", vec![]);
                    let b = recv(new(Some(Writer::Bo)), &root);
                    let (a, one) = edit(a, a1, "1", vec![]);
                    let (_, two) = edit(a, a2, "2", vec![]);
                    let (b, three) = edit(b, b1, "3", vec![]);
                    let (_, four) = edit(b, b2, "4", vec![]);
                    cases.push(case(
                        &format!("gaps-{a1}-{a2}-{b1}-{b2}"),
                        vec![root, one, two, three, four],
                    ));
                }
            }
        }
    }
    println!("[{}]", cases.join(","));
}
