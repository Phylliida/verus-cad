//! Proof-helper modules (kept out of the runtime modules for trigger
//! hygiene, per workspace AGENTS.md).

#[cfg(verus_keep_ghost)]
pub mod rational_raw;

#[cfg(verus_keep_ghost)]
pub mod rpow;

#[cfg(verus_keep_ghost)]
pub mod angle_ledger;

#[cfg(verus_keep_ghost)]
pub mod momentum;
