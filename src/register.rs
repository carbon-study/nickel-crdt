//! Single-write keyed-register checkpoint, without Undo/Redo.
//!
//! Experimental, not an accepted verified API. Caller-supplied u64 writer IDs
//! must be unique and fenced; never fork, roll back or reuse a producer stream.
//! Receiving history does not restore a producer's private counter.
//! Keys are independent u64 application data. Values are opaque byte strings;
//! applications encode their format-family/version tag inside those bytes.
//! Every key starts with the same explicitly configured initial value.
//! All replicas of one document must share that configuration.
//!
//! Every counted write is retained. Read priority is (Lamport, writer); valid
//! clocks strictly increase on causal edges, so a dominated write cannot win.
//! Validation checks the observed value and clock against the exact author past.

use crate::causal::{Event, Id};
use crate::{event_layer as graph, event_shell as shell};



#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    Conflict,
    Missing,
    Invalid,
    ClockExhausted,
    CounterExhausted,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Admission { Added, Duplicate }

#[derive(Clone, Debug)]
pub struct Write {
    pub key: u64,
    pub value: Vec<u8>,
    pub observed: Vec<u8>,
    pub lamport: u64,
}
pub type Fact = Event<Write>;

#[derive(Clone, Debug)]
pub struct Replica {
    writer: u64,
    next_counter: u64,
    initial: Vec<u8>,
    facts: Vec<Fact>,
}

pub fn bytes_equal(a: &[u8], b: &[u8]) -> bool {
    if a.len() != b.len() { return false; }
    for i in 0..a.len() {
        if a[i] != b[i] { return false; }
    }
    true
}

fn write_equal(a: &Write, b: &Write) -> bool {
    a.key == b.key && a.lamport == b.lamport
        && bytes_equal(&a.value, &b.value) && bytes_equal(&a.observed, &b.observed)
}
fn fact_equal(a: &Fact, b: &Fact) -> bool {
    crate::causal::event_equal(a, b, write_equal)
}
fn identity(f: &Fact) -> Id { f.id }
fn parents(f: &Fact) -> &[Id] { &f.after }
fn same_id(a: &Id, b: &Id) -> bool { a.peer == b.peer && a.counter == b.counter }
fn less_id(a: &Id, b: &Id) -> bool {
    a.peer < b.peer || (a.peer == b.peer && a.counter < b.counter)
}
fn copy_fact(f: &Fact) -> Fact { f.clone() }
fn invalid() -> Error { Error::Invalid }
fn missing() -> Error { Error::Missing }
fn previous(id: &Id) -> Option<Id> {
    if id.counter > 1 { Some(Id { peer: id.peer, counter: id.counter - 1 }) }
    else { None }
}
fn forbidden(ancestor: &Id, offered: &Id) -> bool {
    ancestor.peer == offered.peer && ancestor.counter >= offered.counter
}
const OPS: graph::EventOps<Fact, Id, Error> = graph::event_ops(
    graph::graph_ops(identity, parents, same_id, less_id, copy_fact, fact_equal, invalid, missing),
    previous, forbidden, invalid, invalid,
);

/// Strict visible-write priority, not the shared writer-first storage order.
pub fn later(a: &Fact, b: &Fact) -> bool {
    a.payload.lamport > b.payload.lamport
        || (a.payload.lamport == b.payload.lamport && a.id.peer > b.id.peer)
}

/// Native winner scan. Its semantic domain is valid admitted histories.
/// A successful scan returns an index into this exact input, not a cached value.
pub fn winner(facts: &[Fact], key: u64) -> Option<usize> {
    let mut found = None;
    for i in 0..facts.len() {
        if facts[i].payload.key == key {
            match found {
                None => found = Some(i),
                Some(j) => {
                    if j < facts.len() && later(&facts[i], &facts[j]) { found = Some(i); }
                }
            }
        }
    }
    found
}

pub fn read_history(facts: &[Fact], initial: &[u8], key: u64) -> Vec<u8> {
    match winner(facts, key) {
        None => initial.to_vec(),
        Some(i) => {
            if i < facts.len() { facts[i].payload.value.clone() }
            else { initial.to_vec() }
        },
    }
}

/// Every replicated fact advances logical time, even a write to another key.
pub fn next_lamport(facts: &[Fact]) -> Result<u64, Error> {
    let mut highest = 0;
    for i in 0..facts.len() {
        let fact = &facts[i];
        if fact.payload.lamport > highest { highest = fact.payload.lamport; }
    }
    highest.checked_add(1).ok_or(Error::ClockExhausted)
}

impl Replica {
    pub fn new(writer: u64, initial: Vec<u8>) -> Result<Self, Error> {
        Ok(Self { writer, next_counter: 1, initial, facts: Vec::new() })
    }
    pub fn facts(&self) -> &[Fact] { &self.facts }
    pub fn next_counter(&self) -> u64 { self.next_counter }
    pub fn read(&self, key: u64) -> Vec<u8> { read_history(&self.facts, &self.initial, key) }

    /// Duplicate before payload validation. Only a successful detached plan
    /// publishes, through the same shell used by the actual text engine.
    pub fn receive(&mut self, fact: Fact) -> Result<Admission, Error> {
        shell::receive_into(self, &fact, &(), planned, Admission::Added, Admission::Duplicate)
    }

    /// None is an equal-to-observed no-edit: no event, counter or facts change.
    pub fn write(&mut self, key: u64, value: Vec<u8>) -> Result<Option<Fact>, Error> {
        let observed = self.read(key);
        if bytes_equal(&value, &observed) { return Ok(None); }
        let next = self.next_counter.checked_add(1).ok_or(Error::CounterExhausted)?;
        let fact = Fact {
            id: Id { peer: self.writer, counter: self.next_counter },
            after: graph::frontier(&self.facts, &OPS.0)?,
            payload: Write { key, value, observed, lamport: next_lamport(&self.facts)? },
        };
        // Private producer advancement belongs to the detached candidate, too.
        let mut candidate = self.clone();
        match candidate.receive(fact.clone())? {
            Admission::Duplicate => Err(Error::Conflict),
            Admission::Added => {
                candidate.next_counter = next;
                *self = candidate;
                Ok(Some(fact))
            }
        }
    }
}

fn duplicate(_: &(), before: &Replica, fact: &Fact) -> Result<bool, Error> {
    match graph::classify(&before.facts, fact, &OPS.0) {
        None => Ok(false),
        Some(true) => Ok(true),
        Some(false) => Err(Error::Conflict),
    }
}
fn validate(_: &(), before: &Replica, fact: &Fact) -> Result<(), Error> {
    if fact.id.counter == 0 { return Err(Error::Invalid); }
    let selected = graph::validate_event(
        &before.facts, fact, &OPS,
    )?;

    let basis = graph::select_basis(&before.facts, &selected, &OPS.0)?;
    if !bytes_equal(&fact.payload.observed,
        &read_history(&basis, &before.initial, fact.payload.key))
        || bytes_equal(&fact.payload.value, &fact.payload.observed) {
        return Err(Error::Invalid);
    }
    if fact.payload.lamport != next_lamport(&basis)? { return Err(Error::Invalid); }
    Ok(())
}
fn prepare(_: &(), mut next: Replica, fact: &Fact) -> Result<Replica, Error> {
    graph::push(&mut next.facts, fact.clone(), invalid)?;
    Ok(next)
}
fn execute(_: &(), mut next: Replica) -> Result<Replica, Error> {
    next.facts = graph::canonical(&next.facts, &OPS.0)?;
    Ok(next)
}
fn planned(_: &(), before: &Replica, fact: &Fact) -> Result<Option<Replica>, Error> {
    shell::plan(before, fact, &(), duplicate, validate, prepare, execute)
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn exhausted_counter_does_not_turn_noedit_into_an_error() {
        let mut r = Replica::new(7, vec![0]).unwrap();
        r.next_counter = u64::MAX;
        let before = format!("{r:?}");
        assert!(r.write(123, vec![0]).unwrap().is_none());
        assert_eq!(format!("{r:?}"), before);
        assert!(matches!(r.write(123, vec![1]), Err(Error::CounterExhausted)));
        assert_eq!(format!("{r:?}"), before);
    }
    #[test]
    fn logical_clock_overflow_is_explicit() {
        let f = Fact { id: Id { peer: 8, counter: 1 }, after: vec![],
            payload: Write { key: 1, value: vec![1], observed: vec![0], lamport: u64::MAX } };
        assert_eq!(next_lamport(&[f]), Err(Error::ClockExhausted));
    }
    #[test]
    fn received_own_stream_is_not_counter_recovery() {
            let mut old = Replica::new(7, vec![0]).unwrap();
        let fact = old.write(1, vec![1]).unwrap().unwrap();
        let mut restarted = Replica::new(7, vec![0]).unwrap();
        restarted.receive(fact).unwrap();
        let before = format!("{restarted:?}");
        assert!(matches!(restarted.write(1, vec![2]), Err(Error::Conflict)));
        assert_eq!(format!("{restarted:?}"), before);
    }
}
