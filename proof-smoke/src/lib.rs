//! Toolchain smoke test, not a CRDT operation.
pub fn flip(n: usize, mut value: bool) -> bool {
    for _ in 0..n {
        value = !value;
    }
    value
}

#[cfg(test)]
mod tests {
    #[test]
    fn parity_and_involution() {
        for n in 0..64 {
            for value in [false, true] {
                assert_eq!(super::flip(n, value), if n % 2 == 0 { value } else { !value });
                assert_eq!(super::flip(n, super::flip(n, value)), value);
            }
        }
    }
}
