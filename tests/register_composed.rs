// External caller (#105 criterion 1): composes public register operations across
// real replicas under generated schedules, and checks every return and observation
// against an independent expected-history oracle. The oracle encodes the contract
// (docs/register-first-cut.md) directly; it calls no nickel_crdt function.
use nickel_crdt::causal::Id;
use nickel_crdt::register::{Admission, Error, Fact, Replica, Write};
use std::collections::{BTreeMap, BTreeSet};

const KEYS: u64 = 3;
const INITIAL: u8 = 0;

// ---------- independent oracle ----------

#[derive(Clone)]
struct Model {
    writer: u64,
    counter: u64,
    facts: BTreeMap<Id, Fact>, // storage order = id order (writer-first, then counter)
}

fn same(a: &Fact, b: &Fact) -> bool { format!("{a:?}") == format!("{b:?}") }

/// Causal past (inclusive) of `roots` within `facts`, by set closure.
fn closure(facts: &BTreeMap<Id, Fact>, roots: &[Id]) -> BTreeSet<Id> {
    let mut seen: BTreeSet<Id> = BTreeSet::new();
    let mut work: Vec<Id> = roots.to_vec();
    while let Some(id) = work.pop() {
        if seen.insert(id) {
            if let Some(f) = facts.get(&id) { work.extend(f.after.iter().copied()); }
        }
    }
    seen
}

/// Visible value: among writes to `key` in `ids`, the causally maximal ones;
/// the winner is the greatest (lamport, writer). No write: the initial value.
fn read(facts: &BTreeMap<Id, Fact>, ids: &BTreeSet<Id>, key: u64) -> Vec<u8> {
    let writes: Vec<&Fact> = ids.iter().filter_map(|id| facts.get(id)).filter(|f| f.payload.key == key).collect();
    let dominated = |f: &Fact| writes.iter().any(|g| g.id != f.id && closure(facts, &g.after).contains(&f.id));
    writes.iter().copied().filter(|f| !dominated(f))
        .max_by_key(|f| (f.payload.lamport, f.id.peer))
        .map_or(vec![INITIAL], |f| f.payload.value.clone())
}

fn next_clock(facts: &BTreeMap<Id, Fact>, ids: &BTreeSet<Id>) -> u64 {
    ids.iter().filter_map(|id| facts.get(id)).map(|f| f.payload.lamport).max().map_or(1, |m| m + 1)
}

/// Frontier: stored facts that are no other stored fact's direct predecessor.
fn frontier(facts: &BTreeMap<Id, Fact>) -> Vec<Id> {
    let parents: BTreeSet<Id> = facts.values().flat_map(|f| f.after.iter().copied()).collect();
    facts.keys().copied().filter(|id| !parents.contains(id)).collect()
}

impl Model {
    fn all(&self) -> BTreeSet<Id> { self.facts.keys().copied().collect() }

    fn expect_write(&self, key: u64, value: &[u8]) -> (Option<Fact>, Model) {
        let observed = read(&self.facts, &self.all(), key);
        if observed == value { return (None, self.clone()); }
        let fact = Fact {
            id: Id { peer: self.writer, counter: self.counter },
            after: frontier(&self.facts),
            payload: Write { key, value: value.to_vec(), observed, lamport: next_clock(&self.facts, &self.all()) },
        };
        let mut next = self.clone();
        next.facts.insert(fact.id, fact.clone());
        next.counter += 1;
        (Some(fact), next)
    }

    /// Expected admission of an offered fact, from the contract's rules.
    fn expect_receive(&self, f: &Fact) -> (Result<Admission, Error>, Model) {
        if let Some(stored) = self.facts.get(&f.id) {
            return (if same(stored, f) { Ok(Admission::Duplicate) } else { Err(Error::Conflict) }, self.clone());
        }
        let reject = |e| (Err(e), self.clone());
        if f.id.counter == 0 { return reject(Error::Invalid); }
        let distinct: BTreeSet<Id> = f.after.iter().copied().collect();
        if distinct.len() != f.after.len() { return reject(Error::Invalid); }
        if f.after.iter().any(|id| !self.facts.contains_key(id)) { return reject(Error::Missing); }
        let basis = closure(&self.facts, &f.after);
        if f.id.counter > 1 && !basis.contains(&Id { peer: f.id.peer, counter: f.id.counter - 1 }) {
            return reject(Error::Invalid);
        }
        if basis.iter().any(|a| a.peer == f.id.peer && a.counter >= f.id.counter) { return reject(Error::Invalid); }
        if read(&self.facts, &basis, f.payload.key) != f.payload.observed || f.payload.value == f.payload.observed {
            return reject(Error::Invalid);
        }
        if f.payload.lamport != next_clock(&self.facts, &basis) { return reject(Error::Invalid); }
        let mut next = self.clone();
        next.facts.insert(f.id, f.clone());
        (Ok(Admission::Added), next)
    }
}

// ---------- comparison of native observations with the oracle ----------

fn check(r: &Replica, m: &Model, ctx: &str) {
    let expected: Vec<&Fact> = m.facts.values().collect();
    assert_eq!(format!("{:?}", r.facts()), format!("{expected:?}"), "{ctx}: stored facts");
    assert_eq!(r.next_counter(), m.counter, "{ctx}: private counter");
    for key in 0..=KEYS { assert_eq!(r.read(key), read(&m.facts, &m.all(), key), "{ctx}: read key {key}"); }
}

// ---------- generated schedules ----------

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 { self.0 ^= self.0 << 13; self.0 ^= self.0 >> 7; self.0 ^= self.0 << 17; self.0 }
    fn below(&mut self, n: usize) -> usize { (self.next() % n as u64) as usize }
}

/// One single-fault mutation of a fact. Each changes exactly one contract input.
fn mutate(f: &Fact, which: usize) -> Fact {
    let mut g = f.clone();
    match which {
        0 => g.payload.observed = vec![g.payload.observed[0].wrapping_add(7)],
        1 => g.payload.lamport += 1,
        2 => g.payload.lamport = g.payload.lamport.saturating_sub(1),
        3 => g.payload.value = g.payload.observed.clone(),
        4 => g.id.counter = 0,
        5 => { if let Some(&p) = g.after.first() { g.after.push(p) } else { g.after.push(Id { peer: 999, counter: 1 }) } }
        6 => g.after.push(Id { peer: 999, counter: 1 }),
        _ => g.id.counter += 1,
    }
    g
}

#[derive(Default)]
struct Tally { mutated: usize, writes: usize, noedits: usize, added: usize, duplicate: usize, conflict: usize, invalid: usize, missing: usize }

fn run(seed: u64, steps: usize, tally: &mut Tally) {
    let writers = [10u64, 20, 30];
    let mut rng = Rng(seed.wrapping_mul(0x9E37_79B9_7F4A_7C15) | 1);
    let mut native: Vec<Replica> = writers.iter().map(|&w| Replica::new(w, vec![INITIAL]).unwrap()).collect();
    let mut model: Vec<Model> = writers.iter().map(|&w| Model { writer: w, counter: 1, facts: BTreeMap::new() }).collect();
    let mut pool: Vec<Fact> = Vec::new(); // every authored fact
    for step in 0..steps {
        let r = rng.below(native.len());
        let ctx = format!("seed {seed} step {step} replica {r}");
        let op = rng.below(10);
        if op < 4 || pool.is_empty() {
            let key = rng.below(KEYS as usize + 1) as u64;
            let value = vec![rng.below(4) as u8];
            let (want, next) = model[r].expect_write(key, &value);
            let got = native[r].write(key, value).unwrap_or_else(|e| panic!("{ctx}: write failed {e:?}"));
            assert_eq!(format!("{got:?}"), format!("{want:?}"), "{ctx}: authored fact");
            match got { Some(f) => { tally.writes += 1; pool.push(f) } None => tally.noedits += 1 }
            model[r] = next;
        } else {
            let base = pool[rng.below(pool.len())].clone();
            let mut faulted = false;
            let offered = if op < 8 { base } else if op == 8 && model[r].facts.contains_key(&base.id) {
                let mut g = base; g.payload.value = vec![g.payload.value[0].wrapping_add(1)]; g
            } else {
                // Single fault: mutate only an offer this receiver would admit as Added,
                // and keep the mutated ID absent, so no other rule also applies.
                // Missing, Duplicate and Conflict keep their own unmutated cases above.
                let which = rng.below(8);
                let admissible = (0..16).map(|_| &pool[rng.below(pool.len())]).find(|f| {
                    matches!(model[r].expect_receive(f).0, Ok(Admission::Added))
                        && !model[r].facts.contains_key(&mutate(f, which).id)
                });
                match admissible { Some(f) => { tally.mutated += 1; faulted = true; mutate(f, which) } None => base }
            };
            let (want, next) = model[r].expect_receive(&offered);
            assert!(!faulted || want.is_err(), "{ctx}: a single-fault offer must be refused");
            let got = native[r].receive(offered);
            assert_eq!(got, want, "{ctx}: admission");
            match got {
                Ok(Admission::Added) => tally.added += 1,
                Ok(Admission::Duplicate) => tally.duplicate += 1,
                Err(Error::Conflict) => tally.conflict += 1,
                Err(Error::Invalid) => tally.invalid += 1,
                Err(Error::Missing) => tally.missing += 1,
                Err(e) => panic!("{ctx}: unexpected {e:?}"),
            }
            model[r] = next;
        }
        check(&native[r], &model[r], &ctx);
    }
}

#[test]
fn composed_schedules_match_independent_oracle() {
    let mut tally = Tally::default();
    for seed in 1..=300 { run(seed, 80, &mut tally); }
    // Every contract outcome must actually occur, or the run proves less than it says.
    for (name, n) in [("single-fault offer", tally.mutated), ("write", tally.writes), ("no-edit", tally.noedits), ("added", tally.added),
        ("duplicate", tally.duplicate), ("conflict", tally.conflict), ("invalid", tally.invalid), ("missing", tally.missing)] {
        assert!(n > 0, "outcome never exercised: {name}");
        eprintln!("{name}: {n}");
    }
}
