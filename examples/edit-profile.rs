//! Manual, bounded latency diagnostic. Not a benchmark or a worst-case bound.
//! Build once, then run each shape under an external timeout (see the contract).
use nickel_crdt::edit::*;
use std::io::{self, Write};
use std::time::Instant;

fn main() {
    let shape = std::env::args()
        .nth(1)
        .expect("append | prepend | frontloaded-delete");
    assert!(["append", "prepend", "frontloaded-delete"].contains(&shape.as_str()));
    let mut author = Replica::new(Some(Writer::Alice)).unwrap();
    let mut receiver = Replica::new(None).unwrap();
    let mut expected: Vec<(BirthId, u32)> = Vec::new();
    let mut retained = Vec::new();
    let mut author_total = 0u128;
    let mut receive_total = 0u128;
    for step in 1..=128 {
        let deleting = shape == "frontloaded-delete" && step > 8;
        let size = if deleting {
            0
        } else if shape == "frontloaded-delete" {
            64
        } else {
            4
        };
        let gap = if shape == "prepend" || deleting {
            0
        } else {
            expected.len()
        };
        let insert = vec![u32::from('a') + (step % 26) as u32; size];
        let delete = if deleting {
            vec![expected[0].0]
        } else {
            vec![]
        };
        // Input construction and observations/assertions are outside timers.
        // The author timer includes cloning the two request vectors for the call.
        let start = Instant::now();
        let (next, result) = author.edit(gap, insert.clone(), delete.clone());
        let author_us = start.elapsed().as_micros();
        author = next;
        let Local::Authored(fact) = result.expect("profile edit must fit") else {
            panic!("empty edit")
        };
        assert_eq!(
            fact.id,
            EventId {
                writer: Writer::Alice,
                counter: step
            }
        );
        assert_eq!(fact.insert, insert);
        assert_eq!(fact.delete, delete);
        let start = Instant::now();
        let (next, result) = receiver.receive(&fact);
        let receive_us = start.elapsed().as_micros();
        receiver = next;
        assert_eq!(result, Ok(Admission::Added));
        if deleting {
            expected.remove(0);
        } else {
            let added: Vec<_> = insert
                .iter()
                .enumerate()
                .map(|(index, scalar)| {
                    (
                        BirthId {
                            event: EventId {
                                writer: Writer::Alice,
                                counter: step,
                            },
                            index,
                        },
                        *scalar,
                    )
                })
                .collect();
            expected.splice(gap..gap, added.iter().copied());
            retained.splice(gap..gap, added.iter().map(|(id, _)| *id));
        }
        assert_eq!(author.observe().unwrap(), expected);
        assert_eq!(receiver.observe().unwrap(), expected);
        assert_eq!(author.whole().unwrap(), retained);
        assert_eq!(receiver.whole().unwrap(), retained);
        assert_eq!(author.next_counter(), step + 1);
        assert_eq!(receiver.next_counter(), 1);
        author_total += author_us;
        receive_total += receive_us;
        println!("{{\"shape\":\"{shape}\",\"events\":{step},\"births\":{},\"visible\":{},\"author_us\":{author_us},\"receive_us\":{receive_us}}}", retained.len(), expected.len());
        io::stdout().flush().unwrap();
    }
    // Workload size is the caller benchmark budget, not an engine refusal.
    println!("{{\"complete\":true,\"shape\":\"{shape}\",\"author_total_us\":{author_total},\"receive_total_us\":{receive_total}}}");
}
