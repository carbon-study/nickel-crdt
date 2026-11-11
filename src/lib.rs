//! Experimental two-writer edit/admit candidate. Not a verified CRDT release.
//! Structured facts only; no transport, checkpoint, Undo, grouping or anchors.
pub mod edit;

pub mod causal;
pub mod atomic_map;

pub mod event_layer;

pub mod event_shell;
