//! A real external caller across the former policy ceilings.
//! This finite workload size is a harness choice, not engine configuration.
use nickel_crdt::{edit, register};
fn main() {
    // One actual text fact crosses the old per-fact scalar, retained-birth,
    // whole-tree and ordering-link policy ceilings.
    let author = edit::Replica::new(Some(edit::Writer::Alice)).unwrap();
    let scalars = vec![u32::from('x'); 513];
    let (author, result) = author.edit(0, scalars.clone(), vec![]);
    let edit::Local::Authored(fact) = result.unwrap() else { panic!("counted text"); };
    let reader = edit::Replica::new(None).unwrap();
    let (reader, result) = reader.receive(&fact);
    assert_eq!(result, Ok(edit::Admission::Added));
    assert_eq!(author.observe().unwrap(), reader.observe().unwrap());
    assert_eq!(reader.whole().unwrap().len(), 513);
    assert_eq!(reader.observe().unwrap().iter().map(|(_,s)| *s).collect::<Vec<_>>(), scalars);
    let deletes = author.observe().unwrap().iter().map(|(id,_)| *id).collect();
    let (author, result) = author.edit(0, vec![], deletes);
    let edit::Local::Authored(deletion) = result.unwrap() else { panic!("counted deletion"); };
    assert_eq!(deletion.delete.len(), 513);
    let (reader, result) = reader.receive(&deletion);
    assert_eq!(result, Ok(edit::Admission::Added));
    assert!(author.observe().unwrap().is_empty());
    assert_eq!(author.observe().unwrap(), reader.observe().unwrap());
    assert_eq!(reader.whole().unwrap().len(), 513); // retained, not compacted

    // 65 independently fenced writers create 65 concurrent heads. A fully
    // synced replica must still author a counted write citing all 65.
    let mut register = register::Replica::new(1000, vec![]).unwrap();
    let mut observer = register::Replica::new(1001, vec![]).unwrap();
    for peer in 0..65 {
        let mut producer = register::Replica::new(peer, vec![]).unwrap();
        let fact = producer.write(7, vec![peer as u8 + 1]).unwrap().unwrap();
        register.receive(fact.clone()).unwrap();
        observer.receive(fact).unwrap();
    }
    let joined = register.write(7, vec![255; 4097]).unwrap().unwrap();
    assert_eq!(joined.after.len(), 65);
    observer.receive(joined).unwrap();
    // Also cross the old 128-event default profile, retaining every fact.
    for value in 0..64 {
        let fact = register.write(8, vec![value]).unwrap().unwrap();
        observer.receive(fact).unwrap();
    }
    assert_eq!(register.facts().len(), 130);
    assert_eq!(observer.facts().len(), 130);
    assert_eq!(register.read(7), vec![255; 4097]);
    assert_eq!(register.read(7), observer.read(7));
    assert_eq!(register.read(8), observer.read(8));
    println!("actual text: 513 retained births and deletion targets; actual register: 65-head write, 4097-byte value, 130 retained facts");
}
