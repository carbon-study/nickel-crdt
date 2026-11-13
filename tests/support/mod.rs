//! Workload budgets belong to the caller/test harness, never the CRDT engine.
//! This guard runs before semantic admission; it does not reproduce the old
//! engine error precedence. In particular Budget can precede Missing.
use nickel_crdt::edit::{Admission, Error, Fact, Replica};
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Capacity { Events, Births, Scalars, Dependencies, DeleteTargets, OrderingLinks }
#[derive(Clone, Copy)]
pub struct Limits {
    pub events: usize, pub births: usize, pub scalars: usize,
    pub dependencies: usize, pub ordering_links: usize,
}
impl Default for Limits {
    fn default() -> Self {
        Self { events: 128, births: 512, scalars: 64, dependencies: 64, ordering_links: 1536 }
    }
}
#[derive(Debug, PartialEq, Eq)]
pub enum HarnessError { Budget(Capacity), Engine(Error) }
pub fn receive(r: Replica, f: &Fact, b: Limits) -> (Replica, Result<Admission, HarnessError>) {
    // Exact duplicates keep their normal neutral path even at a harness budget.
    if !r.facts().iter().any(|old| old.id == f.id) {
        let Some(total) = r.facts().iter().try_fold(0usize, |n, old| n.checked_add(old.insert.len()))
            .and_then(|n| n.checked_add(f.insert.len())) else {
            return (r, Err(HarnessError::Budget(Capacity::Births)));
        };
        let refusal = if r.facts().len() >= b.events { Some(Capacity::Events) }
        else if f.after.len() > b.dependencies { Some(Capacity::Dependencies) }
        else if f.insert.len() > b.scalars { Some(Capacity::Scalars) }
        else if total > b.births { Some(Capacity::Births) }
        else if f.delete.len() > 512 { Some(Capacity::DeleteTargets) }
        else if total.checked_mul(3).map_or(true, |links| links > b.ordering_links) { Some(Capacity::OrderingLinks) }
        else { None };
        if let Some(reason) = refusal { return (r, Err(HarnessError::Budget(reason))); }
    }
    let (r, outcome) = r.receive(f);
    (r, outcome.map_err(HarnessError::Engine))
}
