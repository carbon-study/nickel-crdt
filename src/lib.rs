//! Experimental CRDT candidates. Not a verified CRDT release.
//! Text uses two writers; the keyed-register checkpoint uses fenced caller IDs.
//! Structured facts only; no transport, checkpoint, Undo, grouping or anchors.
pub mod edit;

pub mod causal;
pub mod atomic_map;

pub mod event_layer;

pub mod event_shell;

pub mod register;
