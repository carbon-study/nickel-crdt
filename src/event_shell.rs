//! Payload-independent planning, publication, and replay shells.
//!
//! Clients supply validation and interpretation callbacks. These functions do
//! not promise rollback of callback side effects or of aliased mutable state.

/// Calculate a detached candidate before the caller chooses to publish it.
/// Duplicate detection precedes validation and candidate construction.
pub fn plan<R: Clone, F, C, E>(
    before: &R,
    fact: &F,
    context: &C,
    duplicate: fn(&C, &R, &F) -> Result<bool, E>,
    validate: fn(&C, &R, &F) -> Result<(), E>,
    prepare: fn(&C, R, &F) -> Result<R, E>,
    execute: fn(&C, R) -> Result<R, E>,
) -> Result<Option<R>, E> {
    if duplicate(context, before, fact)? {
        return Ok(None);
    }
    validate(context, before, fact)?;
    let next = before.clone();
    let next = prepare(context, next, fact)?;
    let next = execute(context, next)?;
    Ok(Some(next))
}

/// Publish exactly a successful candidate; errors and duplicates do not assign.
pub fn receive_into<R, F, E, A, C>(
    state: &mut R,
    fact: &F,
    context: &C,
    plan: fn(&C, &R, &F) -> Result<Option<R>, E>,
    added: A,
    duplicate: A,
) -> Result<A, E> {
    match plan(context, state, fact) {
        Err(error) => Err(error),
        Ok(None) => Ok(duplicate),
        Ok(Some(next)) => {
            *state = next;
            Ok(added)
        }
    }
}

/// Owned-state adapter around the same publication boundary.
pub fn receive<R, F, E, A, C>(
    mut state: R,
    fact: &F,
    context: &C,
    plan: fn(&C, &R, &F) -> Result<Option<R>, E>,
    added: A,
    duplicate: A,
) -> (R, Result<A, E>) {
    let result = receive_into(&mut state, fact, context, plan, added, duplicate);
    (state, result)
}

/// Replay one chosen event per iteration, retaining its operation result for
/// later callbacks and returning the actual completion vector.
pub fn scheduled<F, I: Clone, S, O, E, C>(
    facts: &[F],
    initial: S,
    context: &C,
    id: fn(&F) -> I,
    choose: fn(&C, &[F], &[I]) -> Option<usize>,
    apply: fn(&C, &[F], &F, &[(I, O)], S) -> Result<(S, O), E>,
    internal: fn() -> E,
) -> Result<(S, Vec<I>), E> {
    let mut result = initial;
    let mut done: Vec<I> = Vec::new();
    let mut operations: Vec<(I, O)> = Vec::new();
    for _ in 0..facts.len() {
        let index = choose(context, facts, &done).ok_or(internal())?;
        if index >= facts.len() {
            return Err(internal());
        }
        let event = &facts[index];
        let pair = apply(context, facts, event, &operations, result)?;
        let (next, ops) = pair;
        result = next;
        let event_id = id(event);
        crate::event_layer::push(&mut done, event_id.clone(), internal)?;
        crate::event_layer::push(&mut operations, (event_id, ops), internal)?;
    }
    Ok((result, done))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn duplicate(_: &(), _: &Vec<u8>, fact: &u8) -> Result<bool, u8> {
        if *fact == 0 {
            Ok(true)
        } else if *fact == 1 {
            Err(1)
        } else {
            Ok(false)
        }
    }
    fn validate(_: &(), _: &Vec<u8>, fact: &u8) -> Result<(), u8> {
        if *fact == 2 {
            Err(2)
        } else {
            Ok(())
        }
    }
    fn prepare(_: &(), mut next: Vec<u8>, fact: &u8) -> Result<Vec<u8>, u8> {
        next.push(*fact);
        if *fact == 3 {
            Err(3)
        } else {
            Ok(next)
        }
    }
    fn execute(_: &(), mut next: Vec<u8>) -> Result<Vec<u8>, u8> {
        if next.last() == Some(&4) {
            return Err(4);
        }
        next.push(9);
        Ok(next)
    }
    fn planned(_: &(), before: &Vec<u8>, fact: &u8) -> Result<Option<Vec<u8>>, u8> {
        plan(before, fact, &(), duplicate, validate, prepare, execute)
    }
    #[test]
    fn planning_and_publication_preserve_all_return_branches() {
        for fact in 0..6 {
            let before = vec![8];
            let expected = match fact {
                0 => (before.clone(), Ok(false)),
                1..=4 => (before.clone(), Err(fact)),
                _ => (vec![8, fact, 9], Ok(true)),
            };
            assert_eq!(receive(before, &fact, &(), planned, true, false), expected);
        }
    }
    // Pure Clone need not preserve a native value. Publication must not clone
    // the live input merely to adapt an owned-state interface.
    #[derive(Debug, PartialEq, Eq)]
    struct Odd(u8);
    impl Clone for Odd {
        fn clone(&self) -> Self {
            Self(self.0 + 1)
        }
    }
    fn odd_plan(_: &(), _: &Odd, fact: &u8) -> Result<Option<Odd>, u8> {
        match fact {
            0 => Ok(None),
            1 => Err(1),
            _ => Ok(Some(Odd(9))),
        }
    }
    #[test]
    fn borrowed_publication_never_clones_the_live_input() {
        for fact in 0..3 {
            let mut state = Odd(3);
            let outcome = receive_into(&mut state, &fact, &(), odd_plan, true, false);
            match fact {
                0 => {
                    assert_eq!(state, Odd(3));
                    assert_eq!(outcome, Ok(false));
                }
                1 => {
                    assert_eq!(state, Odd(3));
                    assert_eq!(outcome, Err(1));
                }
                _ => {
                    assert_eq!(state, Odd(9));
                    assert_eq!(outcome, Ok(true));
                }
            }
        }
    }
    fn id(fact: &u8) -> u8 {
        *fact
    }
    fn choose(_: &(), facts: &[u8], done: &[u8]) -> Option<usize> {
        if done.len() < facts.len() {
            Some(facts.len() - 1 - done.len())
        } else {
            None
        }
    }
    fn apply(
        _: &(),
        _: &[u8],
        event: &u8,
        previous: &[(u8, u16)],
        result: u16,
    ) -> Result<(u16, u16), u8> {
        // Every callback receives exactly the previous completion state and its
        // matching operation list, including the first empty prefix.
        assert_eq!(result, previous.iter().map(|(id, _)| u16::from(*id)).sum());
        for (id, operation) in previous {
            assert_eq!(*operation, u16::from(*id) * 2);
        }
        Ok((result + u16::from(*event), u16::from(*event) * 2))
    }
    fn internal() -> u8 {
        255
    }
    fn missing(_: &(), _: &[u8], _: &[u8]) -> Option<usize> {
        None
    }
    fn out_of_range(_: &(), facts: &[u8], _: &[u8]) -> Option<usize> {
        Some(facts.len())
    }
    #[test]
    fn scheduling_retains_actual_tree_operations_and_completion_order() {
        assert_eq!(
            scheduled(&[1, 2, 3], 0, &(), id, choose, apply, internal),
            Ok((6, vec![3, 2, 1]))
        );
        assert_eq!(
            scheduled(&[], 0, &(), id, choose, apply, internal),
            Ok((0, vec![]))
        );
        assert_eq!(
            scheduled(&[1], 0, &(), id, missing, apply, internal),
            Err(255)
        );
        assert_eq!(
            scheduled(&[1], 0, &(), id, out_of_range, apply, internal),
            Err(255)
        );
    }
}
