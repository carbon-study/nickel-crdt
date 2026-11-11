//! Experimental non-text client of the shared causal graph and replay shell.
//!
//! This is an example policy, not Carbon's adopted register/collection API.
//! A payload is an ordered batch. Creation is idempotent; writes require a
//! record in the author's exact causal basis or an earlier batch operation.
//! Replay overwrites in canonical topological order (and batch order within an
//! event), so concurrent writes have a deterministic example winner. Every
//! source event is retained. There is no removal, Restore, Undo or compaction.
//! Format families and versions identify opaque bytes, not interpreted schemas.

use crate::causal::{Event, Id};
use std::collections::{BTreeMap, BTreeSet};

/// Inclusive event and per-event dependency bounds; duplicates bypass both.
/// Zero events forbids additions; zero dependencies permits only root events.
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

pub const MAX_BATCH_OPS: usize = 64;
pub const MAX_NAME_BYTES: usize = 128;
pub const MAX_VALUE_BYTES: usize = 4096;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Value {
    pub family: String,
    pub version: u32,
    pub bytes: Vec<u8>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Op {
    CreateRecord {
        record: String,
    },
    Put {
        record: String,
        field: String,
        value: Value,
    },
}

pub type Batch = Vec<Op>;
pub type State = BTreeMap<String, BTreeMap<String, Value>>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BatchError {
    InvalidBatch,
    InvalidName,
    ValueTooLarge,
    MissingRecord,
    CounterExhausted,
}

fn name_ok(name: &str) -> bool {
    !name.is_empty() && name.len() <= MAX_NAME_BYTES
}

fn apply(state: &mut State, batch: &Batch) -> Result<(), BatchError> {
    if batch.is_empty() || batch.len() > MAX_BATCH_OPS {
        return Err(BatchError::InvalidBatch);
    }
    for op in batch {
        match op {
            Op::CreateRecord { record } => {
                if !name_ok(record) {
                    return Err(BatchError::InvalidName);
                }
                state.entry(record.clone()).or_default();
            }
            Op::Put {
                record,
                field,
                value,
            } => {
                if !name_ok(record) || !name_ok(field) || !name_ok(&value.family) {
                    return Err(BatchError::InvalidName);
                }
                if value.bytes.len() > MAX_VALUE_BYTES {
                    return Err(BatchError::ValueTooLarge);
                }
                state
                    .get_mut(record)
                    .ok_or(BatchError::MissingRecord)?
                    .insert(field.clone(), value.clone());
            }
        }
    }
    Ok(())
}

fn replay(events: &[Event<Batch>]) -> Result<State, BatchError> {
    let mut state = State::new();
    for event in events {
        apply(&mut state, &event.payload)?;
    }
    Ok(state)
}

fn validate(basis: &[Event<Batch>], event: &Event<Batch>) -> Result<(), BatchError> {
    let mut state = replay(basis)?;
    apply(&mut state, &event.payload)
}

fn equal(left: &Batch, right: &Batch) -> bool {
    left == right
}

fn same_event(left: &Event<Batch>, right: &Event<Batch>) -> bool {
    crate::causal::event_equal(left, right, equal)
}

fn event_clone(event: &Event<Batch>) -> Event<Batch> {
    event.clone()
}

fn identity(event: &Event<Batch>) -> Id {
    event.id
}
fn parents(event: &Event<Batch>) -> &[Id] {
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
fn closed_past(facts: &[Event<Batch>], roots: &[Id]) -> Result<Vec<Id>, Error<()>> {
    let selected =
        crate::event_layer::past(facts, roots, identity, parents, id_equal, invalid, missing)?;
    crate::event_layer::validate_after(facts, &selected, identity, id_equal, missing)?;
    Ok(selected)
}

// The batch client rejects malformed whole graphs, including unrelated facts.
// This is stricter than the shared partial-graph helpers and remains client policy.
fn graph_valid(facts: &[Event<Batch>]) -> Result<(), Error<()>> {
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
fn exact_past(facts: &[Event<Batch>], roots: &[Id]) -> Result<Vec<Event<Batch>>, Error<()>> {
    graph_valid(facts)?;
    if crate::event_layer::duplicate_ids(roots, id_equal) {
        return Err(Error::Invalid);
    }
    let selected = closed_past(facts, roots)?;
    crate::event_layer::select_basis(facts, &selected, identity, id_equal, invalid, event_clone)
}

fn choose_scheduled(_: &(), facts: &[Event<Batch>], done: &[Id]) -> Option<usize> {
    crate::event_layer::choose_ready(facts, done, identity, parents, id_equal)
}

fn collect_scheduled(
    _: &(),
    _: &[Event<Batch>],
    event: &Event<Batch>,
    _: &[(Id, ())],
    mut out: Vec<Event<Batch>>,
) -> Result<(Vec<Event<Batch>>, ()), Error<()>> {
    crate::event_layer::push(&mut out, event.clone(), invalid)?;
    Ok((out, ()))
}

/// Repeatedly choose the smallest writer-first id among currently ready facts.
fn schedule(facts: &[Event<Batch>]) -> Result<Vec<Event<Batch>>, Error<()>> {
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

/// A local author shell. The caller owns unique peer allocation; it must not
/// fork or roll this counter back. This is not a persistence/recovery protocol.
/// Receiving an event never repairs the local producer counter.
#[derive(Clone)]
pub struct BatchReplica {
    peer: u64,
    next_counter: u64,
    events: Vec<Event<Batch>>,
    state: State,
    limits: Limits,
}

impl BatchReplica {
    pub fn new(peer: u64, limits: Limits) -> Self {
        Self {
            peer,
            next_counter: 1,
            events: Vec::new(),
            state: State::new(),
            limits,
        }
    }

    pub fn state(&self) -> &State {
        &self.state
    }
    pub fn events(&self) -> &Vec<Event<Batch>> {
        &self.events
    }
    pub fn next_counter(&self) -> u64 {
        self.next_counter
    }

    pub fn receive(&mut self, event: Event<Batch>) -> Result<Admission, Error<BatchError>> {
        crate::event_shell::receive_into(
            self,
            &event,
            &(),
            plan_incoming,
            Admission::Added,
            Admission::Duplicate,
        )
    }

    /// Publish a whole ordered batch or leave facts, materialization and author
    /// counter unchanged. All current heads become the author's causal basis.
    pub fn author(&mut self, payload: Batch) -> Result<Event<Batch>, Error<BatchError>> {
        let next = self
            .next_counter
            .checked_add(1)
            .ok_or(Error::Client(BatchError::CounterExhausted))?;
        let mut heads: BTreeSet<Id> = self.events().iter().map(|event| event.id).collect();
        for event in self.events() {
            for parent in &event.after {
                heads.remove(parent);
            }
        }
        let event = Event {
            id: Id {
                peer: self.peer,
                counter: self.next_counter,
            },
            after: heads.into_iter().collect(),
            payload,
        };
        match self.receive(event.clone())? {
            Admission::Added => {
                self.next_counter = next;
                Ok(event)
            }
            // A reused producer ID is never a newly authored operation.
            Admission::Duplicate => Err(Error::Conflict),
        }
    }
}

fn duplicate(
    _: &(),
    before: &BatchReplica,
    event: &Event<Batch>,
) -> Result<bool, Error<BatchError>> {
    match crate::event_layer::classify(&before.events, event, identity, id_equal, same_event) {
        Some(true) => Ok(true),
        Some(false) => Err(Error::Conflict),
        None => Ok(false),
    }
}
fn validate_incoming(
    _: &(),
    before: &BatchReplica,
    event: &Event<Batch>,
) -> Result<(), Error<BatchError>> {
    if before.events.len() >= before.limits.events || event.after.len() > before.limits.dependencies
    {
        return Err(Error::Capacity);
    }
    let mut candidate = before.events.clone();
    crate::event_layer::push(&mut candidate, event.clone(), invalid)?;
    graph_valid(&candidate).map_err(lift)?;
    let basis = exact_past(&before.events, &event.after).map_err(lift)?;
    validate(&basis, event).map_err(Error::Client)
}
fn prepare_incoming(
    _: &(),
    mut candidate: BatchReplica,
    event: &Event<Batch>,
) -> Result<BatchReplica, Error<BatchError>> {
    crate::event_layer::push(&mut candidate.events, event.clone(), invalid)?;
    Ok(candidate)
}
fn execute_incoming(
    _: &(),
    mut candidate: BatchReplica,
) -> Result<BatchReplica, Error<BatchError>> {
    let ordered = schedule(&candidate.events).map_err(lift)?;
    candidate.state = replay(&ordered).map_err(Error::Client)?;
    Ok(candidate)
}
fn plan_incoming(
    _: &(),
    before: &BatchReplica,
    event: &Event<Batch>,
) -> Result<Option<BatchReplica>, Error<BatchError>> {
    crate::event_shell::plan(
        before,
        event,
        &(),
        duplicate,
        validate_incoming,
        prepare_incoming,
        execute_incoming,
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    fn limits() -> Limits {
        Limits {
            events: 64,
            dependencies: 64,
        }
    }
    fn value(bytes: &[u8]) -> Value {
        Value {
            family: "unknown.application/future".into(),
            version: u32::MAX,
            bytes: bytes.into(),
        }
    }
    fn create(record: &str) -> Op {
        Op::CreateRecord {
            record: record.into(),
        }
    }
    fn put(record: &str, field: &str, bytes: &[u8]) -> Op {
        Op::Put {
            record: record.into(),
            field: field.into(),
            value: value(bytes),
        }
    }
    fn snapshot(replica: &BatchReplica) -> (State, Vec<(Id, Vec<Id>, Batch)>, u64) {
        (
            replica.state().clone(),
            replica
                .events()
                .iter()
                .map(|e| (e.id, e.after.clone(), e.payload.clone()))
                .collect(),
            replica.next_counter(),
        )
    }

    #[test]
    fn multi_field_creation_and_same_key_order_are_atomic() {
        let mut replica = BatchReplica::new(u64::MAX - 1, limits());
        replica
            .author(vec![
                create("card"),
                put("card", "prompt", b"why?"),
                put("card", "answer", &[0, 255, 128]),
                put("card", "prompt", b"how?"),
            ])
            .unwrap();
        assert_eq!(replica.state()["card"]["prompt"], value(b"how?"));
        assert_eq!(replica.state()["card"]["answer"], value(&[0, 255, 128]));
        assert_eq!(replica.events().len(), 1);
        assert_eq!(replica.next_counter(), 2);
        let before = snapshot(&replica);
        assert_eq!(
            replica
                .author(vec![
                    create("unfinished"),
                    put("unfinished", "prompt", b"new"),
                    put("absent", "answer", b"bad")
                ])
                .unwrap_err(),
            Error::Client(BatchError::MissingRecord)
        );
        assert_eq!(snapshot(&replica), before);
    }

    #[test]
    fn causal_and_concurrent_batches_converge_in_two_delivery_orders() {
        let mut a = BatchReplica::new(1 << 40, limits());
        let mut b = BatchReplica::new((1 << 40) + 9, limits());
        let mut c = BatchReplica::new(u64::MAX - 7, limits());
        let root = a
            .author(vec![
                create("card"),
                put("card", "prompt", b"start"),
                put("card", "answer", b"seed"),
            ])
            .unwrap();
        b.receive(root.clone()).unwrap();
        c.receive(root.clone()).unwrap();
        let left = b.author(vec![put("card", "answer", b"left")]).unwrap();
        let right = c.author(vec![put("card", "answer", b"right")]).unwrap();
        let mut first = BatchReplica::new(3, limits());
        let mut second = BatchReplica::new(4, limits());
        for event in [root.clone(), left.clone(), right.clone()] {
            first.receive(event).unwrap();
        }
        for event in [root, right, left] {
            second.receive(event).unwrap();
        }
        assert_eq!(first.state(), second.state());
        assert_eq!(first.state()["card"]["answer"], value(b"right"));
        assert_eq!(first.events().len(), 3);
        let later = first
            .author(vec![put("card", "answer", b"causally later")])
            .unwrap();
        second.receive(later).unwrap();
        assert_eq!(first.state(), second.state());
        assert_eq!(first.state()["card"]["answer"], value(b"causally later"));
        assert_eq!(second.events().len(), 4);
    }

    #[test]
    fn duplicates_conflicts_and_capacity_leave_everything_unchanged() {
        let mut replica = BatchReplica::new(
            777,
            Limits {
                events: 1,
                dependencies: 8,
            },
        );
        let event = replica
            .author(vec![create("card"), put("card", "prompt", b"kept")])
            .unwrap();
        let before = snapshot(&replica);
        assert_eq!(replica.receive(event.clone()), Ok(Admission::Duplicate));
        assert_eq!(snapshot(&replica), before);
        let mut conflicting = event;
        conflicting
            .payload
            .push(put("card", "answer", b"different"));
        assert_eq!(replica.receive(conflicting), Err(Error::Conflict));
        assert_eq!(snapshot(&replica), before);
        assert_eq!(
            replica
                .author(vec![put("card", "prompt", b"overflow")])
                .unwrap_err(),
            Error::Capacity
        );
        assert_eq!(snapshot(&replica), before);
    }

    #[test]
    fn validation_uses_authors_basis_not_receivers_extra_records() {
        let mut replica = BatchReplica::new(91, limits());
        replica.author(vec![create("local-only")]).unwrap();
        let before = snapshot(&replica);
        let invalid = Event {
            id: Id {
                peer: 92,
                counter: 1,
            },
            after: vec![],
            payload: vec![put("local-only", "field", b"not in author basis")],
        };
        assert_eq!(
            replica.receive(invalid),
            Err(Error::Client(BatchError::MissingRecord))
        );
        assert_eq!(snapshot(&replica), before);
    }

    #[test]
    fn received_final_failure_and_payload_bounds_are_transactional() {
        let mut replica = BatchReplica::new(101, limits());
        let root = replica.author(vec![create("card")]).unwrap();
        let before = snapshot(&replica);
        let invalid = Event {
            id: Id {
                peer: 202,
                counter: 1,
            },
            after: vec![root.id],
            payload: vec![
                put("card", "prompt", b"must not escape"),
                put("missing", "answer", b"invalid final operation"),
            ],
        };
        assert_eq!(
            replica.receive(invalid),
            Err(Error::Client(BatchError::MissingRecord))
        );
        assert_eq!(snapshot(&replica), before);
        let mut oversized_value = value(b"");
        oversized_value.bytes = vec![0; MAX_VALUE_BYTES + 1];
        let invalid_batches = vec![
            (vec![], BatchError::InvalidBatch),
            (
                vec![create("card"); MAX_BATCH_OPS + 1],
                BatchError::InvalidBatch,
            ),
            (vec![create("")], BatchError::InvalidName),
            (
                vec![create(&"x".repeat(MAX_NAME_BYTES + 1))],
                BatchError::InvalidName,
            ),
            (
                vec![Op::Put {
                    record: "card".into(),
                    field: "field".into(),
                    value: oversized_value,
                }],
                BatchError::ValueTooLarge,
            ),
        ];
        for (batch, error) in invalid_batches {
            assert_eq!(replica.author(batch).unwrap_err(), Error::Client(error));
            assert_eq!(snapshot(&replica), before);
        }
    }
    fn id(peer: u64, counter: u64) -> Id {
        Id { peer, counter }
    }
    fn event(peer: u64, counter: u64, after: Vec<Id>, payload: i32) -> Event<Batch> {
        Event {
            id: id(peer, counter),
            after,
            payload: vec![create(&payload.to_string())],
        }
    }
    #[test]
    fn neutral_returns_preserve_original_state_with_non_preserving_clone() {
        // The batch state is a concrete owned BTreeMap. This deliberately
        // non-value-preserving owned Clone instead probes the shared publication
        // boundary directly: failed/duplicate plans must retain the original.
        struct Odd(u32);
        impl Clone for Odd {
            fn clone(&self) -> Self {
                Odd(self.0 + 1)
            }
        }
        fn plan(mode: &u8, before: &Odd, _: &()) -> Result<Option<Odd>, &'static str> {
            match mode {
                0 => Ok(None),
                1 => Err("capacity"),
                _ => {
                    let _detached = before.clone();
                    Err("execute")
                }
            }
        }
        let mut original = Odd(0);
        assert_eq!(
            crate::event_shell::receive_into(&mut original, &(), &0, plan, true, false),
            Ok(false)
        );
        assert_eq!(original.0, 0);
        assert_eq!(
            crate::event_shell::receive_into(&mut original, &(), &1, plan, true, false),
            Err("capacity")
        );
        assert_eq!(original.0, 0);
        assert_eq!(
            crate::event_shell::receive_into(&mut original, &(), &2, plan, true, false),
            Err("execute")
        );
        assert_eq!(original.0, 0);
    }

    #[test]
    fn graph_errors_are_neutral_and_predecessor_is_transitive() {
        let mut s = BatchReplica::new(100, limits());
        for f in [
            event(4, 1, vec![], 0),
            event(9, 1, vec![id(4, 1)], 1),
            event(4, 2, vec![id(9, 1)], 2),
        ] {
            s.receive(f).unwrap();
        }
        for (f, error) in [
            (event(7, 0, vec![], 0), Error::Invalid),
            (event(7, 2, vec![], 0), Error::Invalid),
            (event(7, 1, vec![id(99, 1)], 0), Error::Missing),
            (event(7, 1, vec![id(4, 1), id(4, 1)], 0), Error::Invalid),
            (event(7, 1, vec![id(7, 1)], 0), Error::Invalid),
        ] {
            let before = snapshot(&s);
            assert_eq!(s.receive(f), Err(error));
            assert_eq!(snapshot(&s), before);
        }
    }

    #[test]
    fn basis_is_exact_and_stored_order() {
        let facts = vec![
            event(8, 1, vec![], 0),
            event(2, 1, vec![], 1),
            event(3, 1, vec![id(8, 1)], 2),
        ];
        let basis = exact_past(&facts, &[id(3, 1)]).unwrap();
        assert_eq!(
            basis.iter().map(|f| f.id).collect::<Vec<_>>(),
            vec![id(8, 1), id(3, 1)]
        );
        let mut causal_write = BatchReplica::new(901, limits());
        let root = causal_write.author(vec![create("causal-record")]).unwrap();
        let write = Event {
            id: id(902, 1),
            after: vec![root.id],
            payload: vec![put("causal-record", "field", b"requires author basis")],
        };
        assert_eq!(causal_write.receive(write), Ok(Admission::Added));
        let mut replica = BatchReplica::new(100, limits());
        for fact in facts {
            replica.receive(fact).unwrap();
        }
        assert_eq!(
            replica.events().iter().map(|f| f.id).collect::<Vec<_>>(),
            vec![id(8, 1), id(2, 1), id(3, 1)]
        );
    }

    #[test]
    fn hard_zero_and_inclusive_limits() {
        let mut s = BatchReplica::new(
            0,
            Limits {
                events: 0,
                dependencies: 0,
            },
        );
        let before = snapshot(&s);
        assert_eq!(s.receive(event(0, 1, vec![], 0)), Err(Error::Capacity));
        assert_eq!(snapshot(&s), before);
        s.limits.events = 2;
        let root = event(0, 1, vec![], 0);
        s.receive(root.clone()).unwrap();
        let before = snapshot(&s);
        assert_eq!(
            s.receive(event(0, 2, vec![id(0, 1)], 1)),
            Err(Error::Capacity)
        );
        assert_eq!(snapshot(&s), before);
        s.limits.dependencies = 1;
        s.receive(event(0, 2, vec![id(0, 1)], 1)).unwrap();
        let before = snapshot(&s);
        assert_eq!(s.receive(root), Ok(Admission::Duplicate));
        assert_eq!(snapshot(&s), before);
        assert_eq!(s.receive(event(1, 1, vec![], 2)), Err(Error::Capacity));
        assert_eq!(snapshot(&s), before);
    }

    #[test]
    fn ordered_dependencies_are_part_of_duplicate_identity() {
        let mut replica = BatchReplica::new(100, limits());
        replica.receive(event(1, 1, vec![], 0)).unwrap();
        replica.receive(event(2, 1, vec![], 1)).unwrap();
        let child = event(1, 2, vec![id(1, 1), id(2, 1)], 2);
        replica.receive(child.clone()).unwrap();
        let before = snapshot(&replica);
        assert_eq!(replica.receive(child.clone()), Ok(Admission::Duplicate));
        let mut reversed = child;
        reversed.after.reverse();
        assert_eq!(replica.receive(reversed), Err(Error::Conflict));
        assert_eq!(snapshot(&replica), before);
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
