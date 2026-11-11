//! Run with `cargo run --locked --example shared-causal`.
//! Actual text and batch clients share the graph/planning/publication code.
use nickel_crdt::{
    atomic_map::{BatchReplica, Op, Value, Limits},
    edit::{Local, Writer, Replica},
};

fn value(text: &str) -> Value {
    Value {
        family: "example/plain-utf8".into(),
        version: 1,
        bytes: text.as_bytes().to_vec(),
    }
}
fn main() {
    let mut laptop = BatchReplica::new(
        100,
        Limits {
            events: 16,
            dependencies: 8,
        },
    );
    let mut phone = BatchReplica::new(
        u64::MAX,
        Limits {
            events: 16,
            dependencies: 8,
        },
    );
    let created = laptop
        .author(vec![
            Op::CreateRecord {
                record: "card-1".into(),
            },
            Op::Put {
                record: "card-1".into(),
                field: "prompt".into(),
                value: value("what was committed?"),
            },
            Op::Put {
                record: "card-1".into(),
                field: "answer".into(),
                value: value("both fields, together"),
            },
        ])
        .unwrap();
    phone.receive(created).unwrap();
    assert_eq!(phone.state(), laptop.state());
    let before = laptop.state().clone();
    let counter = laptop.next_counter();
    let failed = laptop.author(vec![
        Op::Put {
            record: "card-1".into(),
            field: "answer".into(),
            value: value("must not leak"),
        },
        Op::Put {
            record: "missing".into(),
            field: "answer".into(),
            value: value("reject the whole batch"),
        },
    ]);
    assert!(failed.is_err());
    assert_eq!(&before, laptop.state());
    assert_eq!(counter, laptop.next_counter());
    println!("batch: two fields relayed; invalid final operation left state, history and counter unchanged");
    assert_eq!(laptop.events().len(), 1);

    let text = Replica::new(Some(Writer::Alice), Default::default()).unwrap();
    let (text, authored) = text.edit(0, "hello".chars().map(|c| c as u32).collect(), vec![]);
    let Local::Authored(fact) = authored.unwrap() else {
        panic!("missing text fact")
    };
    let (reader, result) = Replica::new(None, Default::default()).unwrap().receive(&fact);
    result.unwrap();
    assert_eq!(text.observe(), reader.observe());
    let visible: String = reader
        .observe()
        .unwrap()
        .iter()
        .map(|(_, c)| char::from_u32(*c).unwrap())
        .collect();
    println!("text: {visible}; original per-birth identities retained through the shared implementation");
}
