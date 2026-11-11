use nickel_crdt::{
    atomic_map::{BatchReplica, Op, Value},
    causal::Limits,
};

#[test]
fn stored_batch_order_is_preserved_after_record_creation() {
    let mut replica = BatchReplica::new(
        83,
        Limits {
            events: 4,
            dependencies: 4,
        },
    );
    replica
        .author(vec![Op::CreateRecord { record: "r".into() }])
        .unwrap();
    let value = |n| Value {
        family: "independent.example/bytes".into(),
        version: u32::MAX,
        bytes: vec![n, 0, 255],
    };
    replica
        .author(vec![
            Op::Put {
                record: "r".into(),
                field: "f".into(),
                value: value(1),
            },
            Op::Put {
                record: "r".into(),
                field: "f".into(),
                value: value(2),
            },
        ])
        .unwrap();
    assert_eq!(replica.state()["r"]["f"], value(2));
    assert_eq!(replica.events().len(), 2);
    assert_eq!(replica.next_counter(), 3);
}
