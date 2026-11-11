//! Experimental two-writer edit/admit candidate. Not a verified CRDT release.
//! Structured facts only; no transport, checkpoint, Undo, grouping or anchors.
pub mod edit;

pub mod causal;
pub mod shared_text;
pub mod atomic_map;
