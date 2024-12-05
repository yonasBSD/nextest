// Copyright (c) The nextest Contributors
// SPDX-License-Identifier: MIT OR Apache-2.0

//! The test runner.
//!
//! The main structure in this module is [`TestRunner`].

mod dispatcher;
mod imp;
mod internal_events;

#[cfg(unix)]
#[path = "unix.rs"]
mod os;

#[cfg(windows)]
#[path = "windows.rs"]
mod os;

use dispatcher::*;
pub use imp::*;
use internal_events::*;