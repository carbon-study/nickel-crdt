//! Text only: three classes of fact-local invalidity (invalid scalars, duplicate
//! delete targets, placement shape) are rejected as Invalid even while the
//! fact's dependencies are absent. Missing still does not promise eventual
//! admissibility: other permanently inadmissible facts (for example Alice:1
//! citing Alice:2) can still return Missing.
use nickel_crdt::edit::*;

fn absent_dependency() -> EventId {
    EventId { writer: Writer::Bo, counter: 1 }
}
fn fact(insert: Vec<u32>, delete: Vec<BirthId>, gap: Option<usize>) -> Fact {
    Fact { id: EventId { writer: Writer::Alice, counter: 1 }, after: vec![absent_dependency()], insert, delete, gap }
}
fn rejected(f: &Fact) -> Result<Admission, Error> {
    let r = Replica::new(None).unwrap();
    let before = r.clone();
    let (r, result) = r.receive(f);
    assert_eq!(r, before, "rejection must leave the replica unchanged");
    result
}

#[test]
fn invalid_scalar_beats_missing_dependency() {
    assert_eq!(rejected(&fact(vec![0xd800], vec![], Some(0))), Err(Error::Invalid(Invalid::Scalar)));
}

#[test]
fn duplicate_delete_target_beats_missing_dependency() {
    let target = BirthId { event: absent_dependency(), index: 0 };
    assert_eq!(rejected(&fact(vec![], vec![target, target], None)), Err(Error::Invalid(Invalid::DeleteDuplicate)));
}

#[test]
fn placement_shape_beats_missing_dependency() {
    assert_eq!(rejected(&fact(vec![], vec![], Some(0))), Err(Error::Invalid(Invalid::PlacementWithoutBirth)));
    assert_eq!(rejected(&fact(vec![u32::from('x')], vec![], None)), Err(Error::Invalid(Invalid::Gap)));
}

#[test]
fn a_well_formed_fact_with_an_absent_dependency_is_still_missing() {
    // Context-dependent checks (visible deletes, gap bound) stay after causal lookup.
    let target = BirthId { event: absent_dependency(), index: 0 };
    assert_eq!(rejected(&fact(vec![u32::from('x')], vec![target], Some(5))), Err(Error::Missing));
}
