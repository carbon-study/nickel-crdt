//! Experimental single-operation text adapter over the shared event store.
//!
//! The fixed profile is `edit::Limits::default()`. The old text implementation
//! remains the interpretation backend: basis validation and canonical replay
//! rebuild it through its public receive API. This duplicates its graph work;
//! this is not an extracted/proved bridge or an all-return equivalence claim.
//! In particular, shared admission errors need not have the old error priority.
use crate::{causal, edit};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TextPayload {
    pub gap: Option<usize>,
    pub insert: Vec<u32>,
    pub delete: Vec<edit::BirthId>,
}
pub type TextEvent = causal::Event<TextPayload>;
pub type Error = causal::Error<edit::Error>;

fn peer(writer: edit::Writer) -> u64 {
    match writer {
        edit::Writer::Alice => 1,
        edit::Writer::Bo => 2,
    }
}
fn writer(id: causal::Id) -> Result<edit::Writer, Error> {
    match id.peer {
        1 => Ok(edit::Writer::Alice),
        2 => Ok(edit::Writer::Bo),
        _ => Err(causal::Error::Invalid),
    }
}
fn native_id(id: causal::Id) -> Result<edit::EventId, Error> {
    Ok(edit::EventId {
        writer: writer(id)?,
        counter: id.counter,
    })
}
fn shared_id(id: edit::EventId) -> causal::Id {
    causal::Id {
        peer: peer(id.writer),
        counter: id.counter,
    }
}

/// The mapping retains the complete single-operation payload and ordered roots.
pub fn event_from_fact(fact: &edit::Fact) -> TextEvent {
    TextEvent {
        id: shared_id(fact.id),
        after: fact.after.iter().copied().map(shared_id).collect(),
        payload: TextPayload {
            gap: fact.gap,
            insert: fact.insert.clone(),
            delete: fact.delete.clone(),
        },
    }
}
pub fn fact_from_event(event: &TextEvent) -> Result<edit::Fact, Error> {
    Ok(edit::Fact {
        id: native_id(event.id)?,
        after: event
            .after
            .iter()
            .copied()
            .map(native_id)
            .collect::<Result<_, _>>()?,
        gap: event.payload.gap,
        insert: event.payload.insert.clone(),
        delete: event.payload.delete.clone(),
    })
}
fn callback_fact(event: &TextEvent) -> Result<edit::Fact, edit::Error> {
    // The public receive boundary rejects unsupported peers before callbacks.
    fact_from_event(event).map_err(|_| edit::Error::Internal)
}
fn replay(events: &[TextEvent]) -> Result<edit::Replica, edit::Error> {
    let mut replica = edit::Replica::new(None, edit::Limits::default())?;
    for event in events {
        let fact = callback_fact(event)?;
        let (next, result) = replica.receive(&fact);
        result?;
        replica = next;
    }
    Ok(replica)
}
fn validate(basis: &[TextEvent], event: &TextEvent) -> Result<(), edit::Error> {
    let replica = replay(basis)?;
    let (_, result) = replica.receive(&callback_fact(event)?);
    result.map(|_| ())
}
fn equal(left: &TextPayload, right: &TextPayload) -> bool {
    left == right
}

#[derive(Clone)]
pub struct SharedText {
    store: causal::Store<TextPayload, edit::Replica>,
    writer: Option<edit::Writer>,
    next_counter: u64,
}
impl SharedText {
    /// Fixed bounded text profile; arbitrary peers remain a shared-core feature.
    pub fn new(writer: Option<edit::Writer>) -> Self {
        let limits = edit::Limits::default();
        Self {
            store: causal::Store::new(
                edit::Replica::new(None, limits).expect("fixed valid text profile"),
                causal::Limits {
                    events: limits.events,
                    dependencies: limits.dependencies,
                },
            ),
            writer,
            next_counter: 1,
        }
    }
    pub fn events(&self) -> &[TextEvent] {
        self.store.events()
    }
    pub fn facts(&self) -> &[edit::Fact] {
        self.store.state().facts()
    }
    pub fn next_counter(&self) -> u64 {
        self.next_counter
    }
    pub fn observe(&self) -> Result<Vec<(edit::BirthId, u32)>, edit::Error> {
        self.store.state().observe()
    }
    pub fn whole(&self) -> Result<Vec<edit::BirthId>, edit::Error> {
        self.store.state().whole()
    }

    /// Received events never advance the device-local author counter.
    pub fn receive(mut self, event: &TextEvent) -> (Self, Result<causal::Admission, Error>) {
        if let Err(error) = fact_from_event(event) {
            return (self, Err(error));
        }
        let result = self.store.receive(event.clone(), equal, validate, replay);
        (self, result)
    }
    /// One local call authors at most one text operation, retaining old BirthIds.
    pub fn edit(
        self,
        gap: usize,
        insert: Vec<u32>,
        delete: Vec<edit::BirthId>,
    ) -> (Self, Result<edit::Local, Error>) {
        let writer = match self.writer {
            Some(writer) => writer,
            None => {
                return (
                    self,
                    Err(causal::Error::Client(edit::Error::Invalid(
                        edit::Invalid::NoWriter,
                    ))),
                )
            }
        };
        if insert.is_empty() && delete.is_empty() {
            return (self, Ok(edit::Local::Empty));
        }
        if self.next_counter > 9_007_199_254_740_991 {
            return (
                self,
                Err(causal::Error::Client(edit::Error::Capacity(
                    edit::Capacity::Counter,
                ))),
            );
        }
        let after = self
            .facts()
            .iter()
            .filter(|fact| {
                !self
                    .facts()
                    .iter()
                    .any(|child| child.after.contains(&fact.id))
            })
            .map(|fact| fact.id)
            .collect();
        let fact = edit::Fact {
            id: edit::EventId {
                writer,
                counter: self.next_counter,
            },
            after,
            gap: if insert.is_empty() { None } else { Some(gap) },
            insert,
            delete,
        };
        let (mut next, result) = self.receive(&event_from_fact(&fact));
        match result {
            Ok(causal::Admission::Added) => {
                next.next_counter += 1;
                (next, Ok(edit::Local::Authored(fact)))
            }
            Ok(causal::Admission::Duplicate) => (next, Err(causal::Error::Conflict)),
            Err(error) => (next, Err(error)),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn assert_same(old: &edit::Replica, new: &SharedText) {
        assert_eq!(old.facts(), new.facts());
        assert_eq!(old.observe(), new.observe());
        assert_eq!(old.whole(), new.whole());
        assert_eq!(old.next_counter(), new.next_counter());
    }
    fn author(
        old: edit::Replica,
        new: SharedText,
        gap: usize,
        insert: &[u32],
        delete: Vec<edit::BirthId>,
    ) -> (edit::Replica, SharedText, edit::Fact) {
        let (old, result) = old.edit(gap, insert.to_vec(), delete.clone());
        let (new, actual) = new.edit(gap, insert.to_vec(), delete);
        let expected = result.unwrap();
        assert_eq!(actual.unwrap(), expected);
        assert_same(&old, &new);
        let edit::Local::Authored(fact) = expected else {
            panic!("expected authored fact")
        };
        assert_eq!(fact_from_event(&event_from_fact(&fact)).unwrap(), fact);
        (old, new, fact)
    }
    fn deliver(
        old: edit::Replica,
        new: SharedText,
        fact: &edit::Fact,
    ) -> (edit::Replica, SharedText) {
        let (old, expected) = old.receive(fact);
        let (new, actual) = new.receive(&event_from_fact(fact));
        assert_eq!(
            matches!(expected, Ok(edit::Admission::Added)),
            matches!(actual, Ok(causal::Admission::Added))
        );
        assert!(expected.is_ok() && actual.is_ok());
        assert_same(&old, &new);
        (old, new)
    }
    #[test]
    fn two_clients_concurrency_author_basis_delete_and_duplicate_match_old() {
        let a = edit::Replica::new(Some(edit::Writer::Alice), edit::Limits::default()).unwrap();
        let b = edit::Replica::new(Some(edit::Writer::Bo), edit::Limits::default()).unwrap();
        let (a, sa, root) = author(
            a,
            SharedText::new(Some(edit::Writer::Alice)),
            0,
            &[97, 98],
            vec![],
        );
        let (b, sb) = deliver(b, SharedText::new(Some(edit::Writer::Bo)), &root);
        let (a, sa, x) = author(a, sa, 1, &[120], vec![]);
        // Bo's gap is checked against the author's root-only view, even when
        // delivered to Alice after Alice's concurrent extra insertion.
        let (b, sb, y) = author(
            b,
            sb,
            1,
            &[121],
            vec![edit::BirthId {
                event: root.id,
                index: 1,
            }],
        );
        let (a, sa) = deliver(a, sa, &y);
        let (b, sb) = deliver(b, sb, &x);
        assert_eq!(sa.observe(), sb.observe());
        assert_eq!(sa.whole(), sb.whole());
        let (a, sa) = deliver(a, sa, &y);
        let (b, sb) = deliver(b, sb, &x);
        assert_same(&a, &sa);
        assert_same(&b, &sb);
        let (a, sa, _) = author(
            a,
            sa,
            0,
            &[],
            vec![edit::BirthId {
                event: x.id,
                index: 0,
            }],
        );
        assert_same(&a, &sa);
    }
    #[test]
    fn author_basis_capacity_and_counter_failures_are_neutral() {
        let old = edit::Replica::new(Some(edit::Writer::Alice), edit::Limits::default()).unwrap();
        let (old, text, root) = author(
            old,
            SharedText::new(Some(edit::Writer::Alice)),
            0,
            &[97],
            vec![],
        );
        let (_, text, child) = author(old, text, 1, &[98], vec![]);
        let saved = snapshot(&text);
        // This receiver has the target; Bo's supplied author basis does not.
        let invalid = edit::Fact {
            id: edit::EventId {
                writer: edit::Writer::Bo,
                counter: 1,
            },
            after: vec![root.id],
            gap: None,
            insert: vec![],
            delete: vec![edit::BirthId {
                event: child.id,
                index: 0,
            }],
        };
        let (text, result) = text.receive(&event_from_fact(&invalid));
        assert_eq!(
            result,
            Err(causal::Error::Client(edit::Error::Invalid(
                edit::Invalid::DeleteNotVisible
            )))
        );
        assert_eq!(snapshot(&text), saved);
        let (text, result) = text.edit(0, vec![97; 65], vec![]);
        assert_eq!(
            result,
            Err(causal::Error::Client(edit::Error::Capacity(
                edit::Capacity::Scalars
            )))
        );
        assert_eq!(snapshot(&text), saved);
        let mut text = text;
        text.next_counter = 9_007_199_254_740_992;
        let saved = snapshot(&text);
        let (text, result) = text.edit(0, vec![97], vec![]);
        assert_eq!(
            result,
            Err(causal::Error::Client(edit::Error::Capacity(
                edit::Capacity::Counter
            )))
        );
        assert_eq!(snapshot(&text), saved);
        let (text, result) = text.edit(0, vec![], vec![]);
        assert_eq!(result, Ok(edit::Local::Empty));
        assert_eq!(snapshot(&text), saved);
    }
    fn snapshot(text: &SharedText) -> (Vec<edit::Fact>, Vec<(edit::BirthId, u32)>, u64) {
        (
            text.facts().to_vec(),
            text.observe().unwrap(),
            text.next_counter(),
        )
    }
    #[test]
    fn failed_empty_and_duplicate_calls_preserve_state_and_counter() {
        let text = SharedText::new(Some(edit::Writer::Alice));
        let initial = snapshot(&text);
        let (text, result) = text.edit(999, vec![], vec![]);
        assert_eq!(result, Ok(edit::Local::Empty));
        assert_eq!(snapshot(&text), initial);
        let (text, result) = text.edit(1, vec![97], vec![]);
        assert_eq!(
            result,
            Err(causal::Error::Client(edit::Error::Invalid(
                edit::Invalid::Gap
            )))
        );
        assert_eq!(snapshot(&text), initial);
        let (text, result) = text.edit(0, vec![0xd800], vec![]);
        assert_eq!(
            result,
            Err(causal::Error::Client(edit::Error::Invalid(
                edit::Invalid::Scalar
            )))
        );
        assert_eq!(snapshot(&text), initial);
        let (text, result) = text.edit(0, vec![97], vec![]);
        let edit::Local::Authored(fact) = result.unwrap() else {
            panic!()
        };
        let saved = snapshot(&text);
        let event = event_from_fact(&fact);
        let (text, result) = text.receive(&event);
        assert_eq!(result, Ok(causal::Admission::Duplicate));
        assert_eq!(snapshot(&text), saved);
        let mut conflict = event.clone();
        conflict.payload.insert = vec![98];
        let (text, result) = text.receive(&conflict);
        assert_eq!(result, Err(causal::Error::Conflict));
        assert_eq!(snapshot(&text), saved);
        let mut unknown = event.clone();
        unknown.id.peer = 3;
        let (text, result) = text.receive(&unknown);
        assert_eq!(result, Err(causal::Error::Invalid));
        assert_eq!(snapshot(&text), saved);
        let mut missing = event;
        missing.id = causal::Id {
            peer: 2,
            counter: 1,
        };
        missing.after = vec![causal::Id {
            peer: 2,
            counter: 99,
        }];
        let (text, result) = text.receive(&missing);
        assert_eq!(result, Err(causal::Error::Missing));
        assert_eq!(snapshot(&text), saved);
        let reader = SharedText::new(None);
        let saved = snapshot(&reader);
        let (reader, result) = reader.edit(0, vec![], vec![]);
        assert_eq!(
            result,
            Err(causal::Error::Client(edit::Error::Invalid(
                edit::Invalid::NoWriter
            )))
        );
        assert_eq!(snapshot(&reader), saved);
    }
}
