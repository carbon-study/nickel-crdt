// A separately compiled caller of the public crate, not a private test model.
use nickel_crdt::register::{Admission, Replica};

fn main() {
    let mut phone = Replica::new(100, vec![]).unwrap();
    let mut laptop = Replica::new(200, vec![]).unwrap();
    // Bytes stand for the application's opaque family/version/payload envelope.
    let red = phone.write(42, b"color/v1:red".to_vec()).unwrap().unwrap();
    let blue = laptop.write(42, b"color/v1:blue".to_vec()).unwrap().unwrap();
    assert_eq!(phone.receive(blue.clone()), Ok(Admission::Added));
    assert_eq!(laptop.receive(red), Ok(Admission::Added));
    assert_eq!(phone.read(42), b"color/v1:blue");
    assert_eq!(laptop.read(42), phone.read(42));
    assert_eq!(phone.facts().len(), 2); // red was not discarded
    assert!(phone.write(42, b"color/v1:blue".to_vec()).unwrap().is_none());
    let later = phone.write(42, b"color/v1:green".to_vec()).unwrap().unwrap();
    laptop.receive(later).unwrap();
    assert_eq!(phone.read(42), laptop.read(42));
    let before = format!("{phone:?}");
    let mut invalid = blue;
    invalid.payload.observed = b"tampered".to_vec();
    assert!(phone.receive(invalid).is_err());
    assert_eq!(format!("{phone:?}"), before);
    println!("two native replicas: concurrent winner, retained loser, no-edit, causal overwrite, transactional conflict");
}
