//! Experimental bounded causal storage; no local producer or verified claims.
//! Limits are hard inclusive bounds: `events` is the retained event count and
//! `dependencies` is each incoming event's root count. Zero allows no additions
//! or, respectively, only dependency-free events. Duplicates bypass both limits.

#[derive(Clone, Copy, Debug, Eq, PartialOrd, Ord)]
pub struct Id {
    pub peer: u64,
    pub counter: u64,
}

impl PartialEq for Id {
    fn eq(&self, other: &Self) -> bool {
        self.peer == other.peer && self.counter == other.counter
    }
}

#[derive(Clone, Debug)]
pub struct Event<P: Clone> {
    pub id: Id,
    pub after: Vec<Id>,
    pub payload: P,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Limits {
    pub events: usize,
    pub dependencies: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Error<E> {
    Invalid,
    Conflict,
    Missing,
    Capacity,
    Client(E),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Admission {
    Added,
    Duplicate,
}

#[derive(Clone, Debug)]
pub struct Store<P: Clone, S: Clone> {
    events: Vec<Event<P>>,
    state: S,
    limits: Limits,
}

fn ids_eq(left: &[Id], right: &[Id]) -> bool {
    if left.len() != right.len() {
        return false;
    }
    for i in 0..left.len() {
        if left[i] != right[i] {
            return false;
        }
    }
    true
}

pub fn event_equal<P: Clone>(left: &Event<P>, right: &Event<P>, eq: fn(&P, &P) -> bool) -> bool {
    left.id == right.id && ids_eq(&left.after, &right.after) && eq(&left.payload, &right.payload)
}

/// None means a new identity; Some(true) is duplicate relative to the supplied
/// payload predicate. Exact whole-event equality requires exact client equality.
pub fn classify<P: Clone>(
    facts: &[Event<P>],
    fact: &Event<P>,
    eq: fn(&P, &P) -> bool,
) -> Option<bool> {
    for i in 0..facts.len() {
        if facts[i].id == fact.id {
            return Some(event_equal(&facts[i], fact, eq));
        }
    }
    None
}

fn position<P: Clone>(facts: &[Event<P>], id: Id) -> Option<usize> {
    let mut i = 0;
    while i < facts.len() {
        if facts[i].id == id {
            return Some(i);
        }
        i += 1;
    }
    None
}

fn past_marks<P: Clone>(facts: &[Event<P>], roots: &[Id]) -> Result<Vec<bool>, Error<()>> {
    let mut marks = vec![false; facts.len()];
    for root in roots {
        match position(facts, *root) {
            Some(i) => marks[i] = true,
            None => return Err(Error::Missing),
        }
    }
    let mut changed = true;
    while changed {
        changed = false;
        let mut i = 0;
        while i < facts.len() {
            if marks[i] {
                for dep in &facts[i].after {
                    match position(facts, *dep) {
                        Some(j) => {
                            if !marks[j] {
                                marks[j] = true;
                                changed = true;
                            }
                        }
                        None => return Err(Error::Missing),
                    }
                }
            }
            i += 1;
        }
    }
    Ok(marks)
}

// Public helpers reject malformed supplied graphs, including unrelated facts.
fn graph_valid<P: Clone>(facts: &[Event<P>]) -> Result<(), Error<()>> {
    let mut i = 0;
    while i < facts.len() {
        let fact = &facts[i];
        if fact.id.counter == 0 {
            return Err(Error::Invalid);
        }
        let mut j = 0;
        while j < i {
            if facts[j].id == fact.id {
                return Err(Error::Invalid);
            }
            j += 1;
        }
        j = 0;
        while j < fact.after.len() {
            let mut k = 0;
            while k < j {
                if fact.after[k] == fact.after[j] {
                    return Err(Error::Invalid);
                }
                k += 1;
            }
            j += 1;
        }
        let marks = past_marks(facts, &fact.after)?;
        if marks[i] {
            return Err(Error::Invalid);
        }
        if fact.id.counter > 1 {
            let predecessor = Id {
                peer: fact.id.peer,
                counter: fact.id.counter - 1,
            };
            match position(facts, predecessor) {
                Some(j) if marks[j] => (),
                _ => return Err(Error::Invalid),
            }
        }
        i += 1;
    }
    Ok(())
}

/// Exact transitive closure, retaining input storage order. Supplied facts must
/// form a valid whole graph. Repeated roots are invalid, even for an empty past.
pub fn exact_past<P: Clone>(facts: &[Event<P>], roots: &[Id]) -> Result<Vec<Event<P>>, Error<()>> {
    graph_valid(facts)?;
    let mut i = 0;
    while i < roots.len() {
        let mut j = 0;
        while j < i {
            if roots[i] == roots[j] {
                return Err(Error::Invalid);
            }
            j += 1;
        }
        i += 1;
    }
    let marks = past_marks(facts, roots)?;
    let mut result = Vec::new();
    i = 0;
    while i < facts.len() {
        if marks[i] {
            result.push(facts[i].clone());
        }
        i += 1;
    }
    Ok(result)
}

/// Repeatedly choose the smallest writer-first id among currently ready facts.
pub fn schedule<P: Clone>(facts: &[Event<P>]) -> Result<Vec<Event<P>>, Error<()>> {
    graph_valid(facts)?;
    let mut done = vec![false; facts.len()];
    let mut result = Vec::new();
    while result.len() < facts.len() {
        let mut best: Option<usize> = None;
        let mut i = 0;
        while i < facts.len() {
            if !done[i] {
                let mut ready = true;
                for dep in &facts[i].after {
                    match position(facts, *dep) {
                        Some(j) if done[j] => (),
                        _ => ready = false,
                    }
                }
                if ready {
                    match best {
                        Some(j) if facts[j].id <= facts[i].id => (),
                        _ => best = Some(i),
                    }
                }
            }
            i += 1;
        }
        match best {
            Some(i) => {
                done[i] = true;
                result.push(facts[i].clone());
            }
            None => return Err(Error::Invalid),
        }
    }
    Ok(result)
}

fn lift<E>(error: Error<()>) -> Error<E> {
    match error {
        Error::Invalid => Error::Invalid,
        Error::Conflict => Error::Conflict,
        Error::Missing => Error::Missing,
        Error::Capacity => Error::Capacity,
        Error::Client(()) => Error::Invalid,
    }
}

impl<P: Clone, S: Clone> Store<P, S> {
    pub fn new(state: S, limits: Limits) -> Self {
        Self {
            events: Vec::new(),
            state,
            limits,
        }
    }

    pub fn events(&self) -> &Vec<Event<P>> {
        &self.events
    }
    pub fn state(&self) -> &S {
        &self.state
    }

    /// Clients must be pure and clone mutable state without sharing published
    /// mutable storage. External effects and aliased client state are not rolled
    /// back when validation or replay fails.
    pub fn receive<E>(
        &mut self,
        event: Event<P>,
        eq: fn(&P, &P) -> bool,
        validate: fn(&[Event<P>], &Event<P>) -> Result<(), E>,
        replay: fn(&[Event<P>]) -> Result<S, E>,
    ) -> Result<Admission, Error<E>> {
        match classify(&self.events, &event, eq) {
            Some(true) => return Ok(Admission::Duplicate),
            Some(false) => return Err(Error::Conflict),
            None => (),
        }
        if self.events.len() >= self.limits.events || event.after.len() > self.limits.dependencies {
            return Err(Error::Capacity);
        }
        let mut candidate = self.events.clone();
        candidate.push(event.clone());
        // Validating the candidate also checks its counter/predecessor and cycles.
        graph_valid(&candidate).map_err(lift)?;
        let basis = exact_past(&self.events, &event.after).map_err(lift)?;
        validate(&basis, &event).map_err(Error::Client)?;
        let ordered = schedule(&candidate).map_err(lift)?;
        let state = replay(&ordered).map_err(Error::Client)?;
        self.events = candidate;
        self.state = state;
        Ok(Admission::Added)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn id(peer: u64, counter: u64) -> Id {
        Id { peer, counter }
    }
    fn event(peer: u64, counter: u64, after: Vec<Id>, payload: i32) -> Event<i32> {
        Event {
            id: id(peer, counter),
            after,
            payload,
        }
    }
    fn eq(a: &i32, b: &i32) -> bool {
        a == b
    }
    fn valid(_: &[Event<i32>], _: &Event<i32>) -> Result<(), &'static str> {
        Ok(())
    }
    fn replay(facts: &[Event<i32>]) -> Result<Vec<Id>, &'static str> {
        Ok(facts.iter().map(|f| f.id).collect())
    }
    fn forbidden(_: &[Event<i32>], _: &Event<i32>) -> Result<(), &'static str> {
        panic!("duplicate called validate")
    }
    fn forbidden_replay(_: &[Event<i32>]) -> Result<Vec<Id>, &'static str> {
        panic!("duplicate called replay")
    }
    fn store() -> Store<i32, Vec<Id>> {
        Store::new(
            Vec::new(),
            Limits {
                events: 16,
                dependencies: 8,
            },
        )
    }

    #[test]
    fn duplicate_conflict_and_ordered_dependencies() {
        let mut s = store();
        let a = event(1, 1, vec![], 2);
        let b = event(2, 1, vec![], 3);
        s.receive(a.clone(), eq, valid, replay).unwrap();
        s.receive(b, eq, valid, replay).unwrap();
        let c = event(1, 2, vec![id(1, 1), id(2, 1)], 4);
        s.receive(c.clone(), eq, valid, replay).unwrap();
        s.limits = Limits {
            events: 0,
            dependencies: 0,
        };
        assert_eq!(
            s.receive(c.clone(), eq, forbidden, forbidden_replay),
            Ok(Admission::Duplicate)
        );
        let mut changed = c.clone();
        changed.after.reverse();
        assert_eq!(
            s.receive(changed, eq, forbidden, forbidden_replay),
            Err(Error::Conflict)
        );
        let mut changed = a;
        changed.payload += 1;
        assert_eq!(
            s.receive(changed, eq, forbidden, forbidden_replay),
            Err(Error::Conflict)
        );
        assert_eq!(s.events.len(), 3);
    }

    #[test]
    fn validation_and_replay_failures_rollback() {
        fn reject(_: &[Event<i32>], _: &Event<i32>) -> Result<(), &'static str> {
            Err("validate")
        }
        fn reject_replay(_: &[Event<i32>]) -> Result<Vec<Id>, &'static str> {
            Err("replay")
        }
        let mut s = store();
        s.receive(event(8, 1, vec![], 1), eq, valid, replay)
            .unwrap();
        let before = s.state.clone();
        let next = event(8, 2, vec![id(8, 1)], 2);
        assert_eq!(
            s.receive(next.clone(), eq, reject, replay),
            Err(Error::Client("validate"))
        );
        assert_eq!(s.state, before);
        assert_eq!(s.events.len(), 1);
        assert_eq!(
            s.receive(next, eq, valid, reject_replay),
            Err(Error::Client("replay"))
        );
        assert_eq!(s.state, before);
        assert_eq!(s.events.len(), 1);
    }

    #[test]
    fn graph_errors_are_neutral_and_predecessor_is_transitive() {
        let mut s = store();
        s.receive(event(4, 1, vec![], 0), eq, valid, replay)
            .unwrap();
        s.receive(event(9, 1, vec![id(4, 1)], 0), eq, valid, replay)
            .unwrap();
        s.receive(event(4, 2, vec![id(9, 1)], 0), eq, valid, replay)
            .unwrap();
        for (f, error) in [
            (event(7, 0, vec![], 0), Error::Invalid),
            (event(7, 2, vec![], 0), Error::Invalid),
            (event(7, 1, vec![id(99, 1)], 0), Error::Missing),
            (event(7, 1, vec![id(4, 1), id(4, 1)], 0), Error::Invalid),
            (event(7, 1, vec![id(7, 1)], 0), Error::Invalid),
        ] {
            let old = s.state.clone();
            assert_eq!(s.receive(f, eq, forbidden, forbidden_replay), Err(error));
            assert_eq!(s.events.len(), 3);
            assert_eq!(s.state, old);
        }
    }

    #[test]
    fn basis_is_exact_and_stored_order() {
        fn check(basis: &[Event<i32>], _: &Event<i32>) -> Result<(), &'static str> {
            assert_eq!(
                basis.iter().map(|f| f.id).collect::<Vec<_>>(),
                vec![id(8, 1), id(3, 1)]
            );
            Ok(())
        }
        let mut s = store();
        for f in [
            event(8, 1, vec![], 0),
            event(2, 1, vec![], 0),
            event(3, 1, vec![id(8, 1)], 0),
        ] {
            s.receive(f, eq, valid, replay).unwrap();
        }
        s.receive(event(9, 1, vec![id(3, 1)], 0), eq, check, replay)
            .unwrap();
    }

    #[test]
    fn hard_zero_and_inclusive_limits() {
        let mut s = Store::new(
            Vec::new(),
            Limits {
                events: 0,
                dependencies: 0,
            },
        );
        assert_eq!(
            s.receive(event(0, 1, vec![], 0), eq, valid, replay),
            Err(Error::Capacity)
        );
        s.limits.events = 2;
        s.receive(event(0, 1, vec![], 0), eq, valid, replay)
            .unwrap();
        assert_eq!(
            s.receive(event(0, 2, vec![id(0, 1)], 0), eq, valid, replay),
            Err(Error::Capacity)
        );
        s.limits.dependencies = 1;
        s.receive(event(0, 2, vec![id(0, 1)], 0), eq, valid, replay)
            .unwrap();
        assert_eq!(
            s.receive(event(1, 1, vec![], 0), eq, valid, replay),
            Err(Error::Capacity)
        );
        assert_eq!(s.events.len(), 2);
    }

    #[test]
    fn independent_closure_and_schedule_oracles_all_small_dags() {
        // Edges point to earlier source indices. Every three-node DAG and every
        // storage permutation is checked against matrix closure / permutation
        // enumeration, rather than the implementation's worklist/ready scan.
        let permutations = [
            [0, 1, 2],
            [0, 2, 1],
            [1, 0, 2],
            [1, 2, 0],
            [2, 0, 1],
            [2, 1, 0],
        ];
        for mask in 0..8 {
            let mut edges = [[false; 3]; 3];
            edges[1][0] = mask & 1 != 0;
            edges[2][0] = mask & 2 != 0;
            edges[2][1] = mask & 4 != 0;
            let mut closure = edges;
            for k in 0..3 {
                for i in 0..3 {
                    for j in 0..3 {
                        closure[i][j] |= closure[i][k] && closure[k][j];
                    }
                }
            }
            let ids = [id(30, 1), id(10, 1), id(20, 1)];
            let mut source = Vec::new();
            for i in 0..3 {
                let mut after = Vec::new();
                for j in 0..3 {
                    if edges[i][j] {
                        after.push(ids[j]);
                    }
                }
                source.push(event(ids[i].peer, 1, after, i as i32));
            }
            let mut expected_orders = Vec::new();
            for p in permutations {
                let mut legal = true;
                for i in 0..3 {
                    for j in 0..3 {
                        if edges[i][j]
                            && p.iter().position(|x| *x == j) > p.iter().position(|x| *x == i)
                        {
                            legal = false;
                        }
                    }
                }
                if legal {
                    expected_orders.push(p.map(|i| ids[i]).to_vec());
                }
            }
            expected_orders.sort();
            for p in permutations {
                let facts: Vec<_> = p.iter().map(|i| source[*i].clone()).collect();
                let actual: Vec<_> = schedule(&facts).unwrap().iter().map(|f| f.id).collect();
                assert_eq!(actual, expected_orders[0]);
                for roots_mask in 0..8 {
                    let roots: Vec<_> = (0..3)
                        .filter(|i| roots_mask & (1 << i) != 0)
                        .map(|i| ids[i])
                        .collect();
                    let expected: Vec<_> = p
                        .iter()
                        .filter(|j| {
                            (0..3).any(|i| {
                                roots_mask & (1 << i) != 0 && (i == **j || closure[i][**j])
                            })
                        })
                        .map(|j| ids[*j])
                        .collect();
                    let actual: Vec<_> = exact_past(&facts, &roots)
                        .unwrap()
                        .iter()
                        .map(|f| f.id)
                        .collect();
                    assert_eq!(actual, expected);
                }
            }
        }
    }

    #[test]
    fn helpers_reject_malformed_graphs() {
        let cycle = vec![
            event(1, 1, vec![id(2, 1)], 0),
            event(2, 1, vec![id(1, 1)], 0),
        ];
        assert!(matches!(schedule(&cycle), Err(Error::Invalid)));
        assert!(matches!(exact_past(&cycle, &[]), Err(Error::Invalid)));
        let facts = vec![event(1, 1, vec![], 0)];
        assert!(matches!(
            exact_past(&facts, &[id(1, 1), id(1, 1)]),
            Err(Error::Invalid)
        ));
        assert!(matches!(
            exact_past(&facts, &[id(2, 1)]),
            Err(Error::Missing)
        ));
        let duplicate = vec![facts[0].clone(), facts[0].clone()];
        assert!(matches!(schedule(&duplicate), Err(Error::Invalid)));
    }
}
