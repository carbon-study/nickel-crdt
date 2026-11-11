//! Experimental non-text client for the shared causal store.
//!
//! This is an example policy, not Carbon's adopted register/collection API.
//! A payload is an ordered batch. Creation is idempotent; writes require a
//! record in the author's exact causal basis or an earlier batch operation.
//! Replay overwrites in canonical topological order (and batch order within an
//! event), so concurrent writes have a deterministic example winner. Every
//! source event is retained. There is no removal, Restore, Undo or compaction.
//! Format families and versions identify opaque bytes, not interpreted schemas.

use crate::causal::{Admission, Error, Event, Id, Limits, Store};
use std::collections::{BTreeMap, BTreeSet};

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

/// A local author shell. The caller owns unique peer allocation; it must not
/// fork or roll this counter back. This is not a persistence/recovery protocol.
/// Receiving an event never repairs the local producer counter.
pub struct BatchReplica {
    peer: u64,
    next_counter: u64,
    store: Store<Batch, State>,
}

impl BatchReplica {
    pub fn new(peer: u64, limits: Limits) -> Self {
        Self {
            peer,
            next_counter: 1,
            store: Store::new(State::new(), limits),
        }
    }

    pub fn state(&self) -> &State {
        self.store.state()
    }
    pub fn events(&self) -> &Vec<Event<Batch>> {
        self.store.events()
    }
    pub fn next_counter(&self) -> u64 {
        self.next_counter
    }

    pub fn receive(&mut self, event: Event<Batch>) -> Result<Admission, Error<BatchError>> {
        self.store.receive(event, equal, validate, replay)
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
}
