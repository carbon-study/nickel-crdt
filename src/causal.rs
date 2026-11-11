//! Envelope identity and whole-event equality for the non-text example.
//! Graph scheduling and publication belong to event_layer/event_shell; this
//! module only supplies the concrete peer/counter envelope and its classifier.

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
