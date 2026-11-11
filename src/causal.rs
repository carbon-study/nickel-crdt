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

fn event_clone<P: Clone>(event: &Event<P>) -> Event<P> {
    event.clone()
}

fn identity<P: Clone>(event: &Event<P>) -> Id {
    event.id
}
fn parents<P: Clone>(event: &Event<P>) -> &[Id] {
    &event.after
}
fn id_equal(left: &Id, right: &Id) -> bool {
    left == right
}
fn id_less(left: &Id, right: &Id) -> bool {
    left < right
}
fn invalid<E>() -> Error<E> {
    Error::Invalid
}
fn missing<E>() -> Error<E> {
    Error::Missing
}

// Unlike the shared partial-graph closure, this client's policy rejects any
// unresolved transitive predecessor, including in unrelated supplied facts.
fn closed_past<P: Clone>(facts: &[Event<P>], roots: &[Id]) -> Result<Vec<Id>, Error<()>> {
    let selected =
        crate::event_layer::past(facts, roots, identity, parents, id_equal, invalid, missing)?;
    crate::event_layer::validate_after(facts, &selected, identity, id_equal, missing)?;
    Ok(selected)
}

// Public helpers reject malformed supplied graphs, including unrelated facts.
fn graph_valid<P: Clone>(facts: &[Event<P>]) -> Result<(), Error<()>> {
    // The original position-based malformed-graph policy resolves a repeated
    // ID to its first occurrence until that duplicate is itself rejected.
    // Preserve that error precedence while using the shared closure.
    let mut first = Vec::new();
    for fact in facts {
        if !crate::event_layer::has_fact(&first, &fact.id, identity, id_equal) {
            crate::event_layer::push(&mut first, fact.clone(), invalid)?;
        }
    }
    for i in 0..facts.len() {
        let fact = &facts[i];
        if fact.id.counter == 0 {
            return Err(Error::Invalid);
        }
        if crate::event_layer::has_fact(&facts[..i], &fact.id, identity, id_equal) {
            return Err(Error::Invalid);
        }
        if crate::event_layer::duplicate_ids(&fact.after, id_equal) {
            return Err(Error::Invalid);
        }
        let selected = closed_past(&first, &fact.after)?;
        if crate::event_layer::has_id(&selected, &fact.id, id_equal) {
            return Err(Error::Invalid);
        }
        if fact.id.counter > 1 {
            let predecessor = Id {
                peer: fact.id.peer,
                counter: fact.id.counter - 1,
            };
            if !crate::event_layer::has_id(&selected, &predecessor, id_equal) {
                return Err(Error::Invalid);
            }
        }
    }
    Ok(())
}

/// Exact transitive closure, retaining input storage order. Supplied facts must
/// form a valid whole graph. Repeated roots are invalid, even for an empty past.
pub fn exact_past<P: Clone>(facts: &[Event<P>], roots: &[Id]) -> Result<Vec<Event<P>>, Error<()>> {
    graph_valid(facts)?;
    if crate::event_layer::duplicate_ids(roots, id_equal) {
        return Err(Error::Invalid);
    }
    let selected = closed_past(facts, roots)?;
    crate::event_layer::select_basis(facts, &selected, identity, id_equal, invalid, event_clone)
}

fn choose_scheduled<P: Clone>(_: &(), facts: &[Event<P>], done: &[Id]) -> Option<usize> {
    crate::event_layer::choose_ready(facts, done, identity, parents, id_equal)
}

fn collect_scheduled<P: Clone>(
    _: &(),
    _: &[Event<P>],
    event: &Event<P>,
    _: &[(Id, ())],
    mut out: Vec<Event<P>>,
) -> Result<(Vec<Event<P>>, ()), Error<()>> {
    crate::event_layer::push(&mut out, event.clone(), invalid)?;
    Ok((out, ()))
}

/// Repeatedly choose the smallest writer-first id among currently ready facts.
pub fn schedule<P: Clone>(facts: &[Event<P>]) -> Result<Vec<Event<P>>, Error<()>> {
    graph_valid(facts)?;
    // The shared ready scan uses input order. Canonicalize a detached view, not
    // the retained admission-order event store, to select the least ready ID.
    let ordered =
        crate::event_layer::canonical(facts, identity, id_equal, id_less, invalid, event_clone)?;
    let (result, _) = crate::event_shell::scheduled(
        &ordered,
        Vec::new(),
        &(),
        identity,
        choose_scheduled,
        collect_scheduled,
        invalid,
    )?;
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

struct Client<P: Clone, S: Clone, E> {
    eq: fn(&P, &P) -> bool,
    validate: fn(&[Event<P>], &Event<P>) -> Result<(), E>,
    replay: fn(&[Event<P>]) -> Result<S, E>,
}

fn duplicate<P: Clone, S: Clone, E>(
    client: &Client<P, S, E>,
    before: &Store<P, S>,
    event: &Event<P>,
) -> Result<bool, Error<E>> {
    match classify(&before.events, event, client.eq) {
        Some(true) => Ok(true),
        Some(false) => Err(Error::Conflict),
        None => Ok(false),
    }
}

fn validate_incoming<P: Clone, S: Clone, E>(
    client: &Client<P, S, E>,
    before: &Store<P, S>,
    event: &Event<P>,
) -> Result<(), Error<E>> {
    if before.events.len() >= before.limits.events || event.after.len() > before.limits.dependencies
    {
        return Err(Error::Capacity);
    }
    let mut candidate = before.events.clone();
    crate::event_layer::push(&mut candidate, event.clone(), invalid)?;
    graph_valid(&candidate).map_err(lift)?;
    let basis = exact_past(&before.events, &event.after).map_err(lift)?;
    (client.validate)(&basis, event).map_err(Error::Client)
}

fn prepare_incoming<P: Clone, S: Clone, E>(
    _: &Client<P, S, E>,
    mut candidate: Store<P, S>,
    event: &Event<P>,
) -> Result<Store<P, S>, Error<E>> {
    crate::event_layer::push(&mut candidate.events, event.clone(), invalid)?;
    Ok(candidate)
}

fn execute_incoming<P: Clone, S: Clone, E>(
    client: &Client<P, S, E>,
    mut candidate: Store<P, S>,
) -> Result<Store<P, S>, Error<E>> {
    let ordered = schedule(&candidate.events).map_err(lift)?;
    candidate.state = (client.replay)(&ordered).map_err(Error::Client)?;
    Ok(candidate)
}

fn plan_incoming<P: Clone, S: Clone, E>(
    client: &Client<P, S, E>,
    before: &Store<P, S>,
    event: &Event<P>,
) -> Result<Option<Store<P, S>>, Error<E>> {
    crate::event_shell::plan(
        before,
        event,
        client,
        duplicate,
        validate_incoming,
        prepare_incoming,
        execute_incoming,
    )
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
        let client = Client {
            eq,
            validate,
            replay,
        };
        crate::event_shell::receive_into(
            self,
            &event,
            &client,
            plan_incoming,
            Admission::Added,
            Admission::Duplicate,
        )
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
    fn neutral_returns_preserve_original_state_with_non_preserving_clone() {
        // Pure, owned Clone need not preserve the observed value. A failed
        // detached candidate must never replace the original published state.
        struct Odd(u32);
        impl Clone for Odd {
            fn clone(&self) -> Self {
                Self(self.0 + 1)
            }
        }
        fn replay_odd(_: &[Event<i32>]) -> Result<Odd, &'static str> {
            Ok(Odd(77))
        }
        fn reject(_: &[Event<i32>], _: &Event<i32>) -> Result<(), &'static str> {
            Err("validate")
        }
        fn reject_replay(_: &[Event<i32>]) -> Result<Odd, &'static str> {
            Err("replay")
        }
        let mut s = Store::new(
            Odd(0),
            Limits {
                events: 0,
                dependencies: 8,
            },
        );
        let first = event(1, 1, vec![], 9);
        assert_eq!(
            s.receive(first.clone(), eq, valid, replay_odd),
            Err(Error::Capacity)
        );
        assert_eq!(s.state().0, 0);
        assert!(s.events().is_empty());
        s.limits.events = 4;
        assert_eq!(
            s.receive(first.clone(), eq, valid, replay_odd),
            Ok(Admission::Added)
        );
        assert_eq!(s.state().0, 77);
        assert_eq!(
            s.receive(first, eq, forbidden, reject_replay),
            Ok(Admission::Duplicate)
        );
        assert_eq!(s.state().0, 77);
        assert_eq!(
            s.receive(event(1, 1, vec![], 10), eq, forbidden, reject_replay),
            Err(Error::Conflict)
        );
        assert_eq!(s.state().0, 77);
        assert_eq!(
            s.receive(
                event(2, 1, vec![id(99, 1)], 0),
                eq,
                forbidden,
                reject_replay
            ),
            Err(Error::Missing)
        );
        assert_eq!(s.state().0, 77);
        let next = event(2, 1, vec![], 0);
        assert_eq!(
            s.receive(next.clone(), eq, reject, replay_odd),
            Err(Error::Client("validate"))
        );
        assert_eq!(s.state().0, 77);
        assert_eq!(
            s.receive(next, eq, valid, reject_replay),
            Err(Error::Client("replay"))
        );
        assert_eq!(s.state().0, 77);
        assert_eq!(s.events().len(), 1);
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
    fn duplicate_error_precedes_dependencies_of_ignored_duplicate() {
        let facts = vec![
            event(2, 1, vec![id(1, 1)], 0),
            event(1, 1, vec![], 0),
            event(1, 1, vec![id(99, 1)], 0),
        ];
        assert!(matches!(schedule(&facts), Err(Error::Invalid)));
        assert!(matches!(exact_past(&facts, &[]), Err(Error::Invalid)));
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
