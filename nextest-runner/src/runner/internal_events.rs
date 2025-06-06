// Copyright (c) The nextest Contributors
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Internal events used between the runner components.
//!
//! These events often mirror those in [`crate::reporter::events`], but are used
//! within the runner. They'll often carry additional information that the
//! reporter doesn't need to know about.

use super::{SetupScriptPacket, TestPacket};
use crate::{
    config::{ScriptId, SetupScriptConfig},
    list::TestInstance,
    reporter::{
        TestOutputDisplay,
        events::{
            ExecuteStatus, ExecutionResult, InfoResponse, RetryData, SetupScriptEnvMap,
            SetupScriptExecuteStatus, UnitState,
        },
    },
    signal::ShutdownEvent,
    test_output::ChildExecutionOutput,
    time::StopwatchSnapshot,
};
use nextest_metadata::MismatchReason;
use std::time::Duration;
use tokio::{
    sync::{
        mpsc::{UnboundedReceiver, UnboundedSender},
        oneshot,
    },
    task::JoinError,
};

/// An internal event.
///
/// These events are sent by the executor (the part that actually runs
/// executables) to the dispatcher (the part of the runner that coordinates with
/// the external world).
#[derive(Debug)]
pub(super) enum ExecutorEvent<'a> {
    SetupScriptStarted {
        script_id: ScriptId,
        config: &'a SetupScriptConfig,
        program: String,
        index: usize,
        total: usize,
        // See the note in the `Started` variant.
        req_rx_tx: oneshot::Sender<UnboundedReceiver<RunUnitRequest<'a>>>,
    },
    SetupScriptSlow {
        script_id: ScriptId,
        config: &'a SetupScriptConfig,
        program: String,
        elapsed: Duration,
        will_terminate: Option<Duration>,
    },
    SetupScriptFinished {
        script_id: ScriptId,
        config: &'a SetupScriptConfig,
        program: String,
        index: usize,
        total: usize,
        status: SetupScriptExecuteStatus,
    },
    Started {
        test_instance: TestInstance<'a>,
        // The channel over which to return the unit request.
        //
        // The callback context is solely responsible for coordinating the
        // creation of all channels, such that it acts as the source of truth
        // for which units to broadcast messages out to. This oneshot channel is
        // used to let each test instance know to go ahead and start running
        // tests.
        //
        // Why do we use unbounded channels? Mostly to make life simpler --
        // these are low-traffic channels that we don't expect to be backed up.
        req_rx_tx: oneshot::Sender<UnboundedReceiver<RunUnitRequest<'a>>>,
    },
    Slow {
        test_instance: TestInstance<'a>,
        retry_data: RetryData,
        elapsed: Duration,
        will_terminate: Option<Duration>,
    },
    AttemptFailedWillRetry {
        test_instance: TestInstance<'a>,
        failure_output: TestOutputDisplay,
        run_status: ExecuteStatus,
        delay_before_next_attempt: Duration,
    },
    RetryStarted {
        test_instance: TestInstance<'a>,
        retry_data: RetryData,
        // This is used to indicate that the dispatcher still wants to run the test.
        tx: oneshot::Sender<()>,
    },
    Finished {
        test_instance: TestInstance<'a>,
        success_output: TestOutputDisplay,
        failure_output: TestOutputDisplay,
        junit_store_success_output: bool,
        junit_store_failure_output: bool,
        last_run_status: ExecuteStatus,
    },
    Skipped {
        test_instance: TestInstance<'a>,
        reason: MismatchReason,
    },
}

#[derive(Clone, Copy)]
pub(super) enum UnitExecuteStatus<'a, 'status> {
    Test(&'status InternalExecuteStatus<'a>),
    SetupScript(&'status InternalSetupScriptExecuteStatus<'a>),
}

impl<'a> UnitExecuteStatus<'a, '_> {
    pub(super) fn info_response(&self) -> InfoResponse<'a> {
        match self {
            Self::Test(status) => status.test.info_response(
                UnitState::Exited {
                    result: status.result,
                    time_taken: status.stopwatch_end.active,
                    slow_after: status.slow_after,
                },
                status.output.clone(),
            ),
            Self::SetupScript(status) => status.script.info_response(
                UnitState::Exited {
                    result: status.result,
                    time_taken: status.stopwatch_end.active,
                    slow_after: status.slow_after,
                },
                status.output.clone(),
            ),
        }
    }
}

pub(super) struct InternalExecuteStatus<'a> {
    pub(super) test: TestPacket<'a>,
    pub(super) slow_after: Option<Duration>,
    pub(super) output: ChildExecutionOutput,
    pub(super) result: ExecutionResult,
    pub(super) stopwatch_end: StopwatchSnapshot,
}

impl InternalExecuteStatus<'_> {
    pub(super) fn into_external(self) -> ExecuteStatus {
        ExecuteStatus {
            retry_data: self.test.retry_data(),
            output: self.output,
            result: self.result,
            start_time: self.stopwatch_end.start_time.fixed_offset(),
            time_taken: self.stopwatch_end.active,
            is_slow: self.slow_after.is_some(),
            delay_before_start: self.test.delay_before_start(),
        }
    }
}

pub(super) struct InternalSetupScriptExecuteStatus<'a> {
    pub(super) script: SetupScriptPacket<'a>,
    pub(super) slow_after: Option<Duration>,
    pub(super) output: ChildExecutionOutput,
    pub(super) result: ExecutionResult,
    pub(super) stopwatch_end: StopwatchSnapshot,
    pub(super) env_map: Option<SetupScriptEnvMap>,
}

impl InternalSetupScriptExecuteStatus<'_> {
    pub(super) fn into_external(self) -> SetupScriptExecuteStatus {
        SetupScriptExecuteStatus {
            output: self.output,
            result: self.result,
            start_time: self.stopwatch_end.start_time.fixed_offset(),
            time_taken: self.stopwatch_end.active,
            is_slow: self.slow_after.is_some(),
            env_map: self.env_map,
        }
    }
}

/// Events sent from the dispatcher to individual unit execution tasks.
#[derive(Clone, Debug)]
pub(super) enum RunUnitRequest<'a> {
    Signal(SignalRequest),
    /// Non-signal cancellation requests (e.g. test failures) which should cause
    /// tests to exit in some states.
    OtherCancel,
    Query(RunUnitQuery<'a>),
}

impl<'a> RunUnitRequest<'a> {
    pub(super) fn drain(self, status: UnitExecuteStatus<'a, '_>) {
        match self {
            #[cfg(unix)]
            Self::Signal(SignalRequest::Stop(sender)) => {
                // The receiver being dead isn't really important.
                let _ = sender.send(());
            }
            #[cfg(unix)]
            Self::Signal(SignalRequest::Continue) => {}
            Self::Signal(SignalRequest::Shutdown(_)) => {}
            Self::OtherCancel => {}
            Self::Query(RunUnitQuery::GetInfo(tx)) => {
                // The receiver being dead isn't really important.
                _ = tx.send(status.info_response());
            }
        }
    }
}

#[derive(Clone, Debug)]
pub(super) enum SignalRequest {
    // The mpsc sender is used by each test to indicate that the stop signal has been sent.
    #[cfg(unix)]
    Stop(UnboundedSender<()>),
    #[cfg(unix)]
    Continue,
    Shutdown(ShutdownRequest),
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub(super) enum ShutdownRequest {
    Once(ShutdownEvent),
    Twice,
}

#[derive(Clone, Debug)]
pub(super) enum RunUnitQuery<'a> {
    GetInfo(UnboundedSender<InfoResponse<'a>>),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum InternalTerminateReason {
    Timeout,
    Signal(ShutdownRequest),
}

pub(super) enum RunnerTaskState {
    Finished { child_join_errors: Vec<JoinError> },
    Cancelled,
}

impl RunnerTaskState {
    /// Mark a runner task as finished and having not run any children.
    pub(super) fn finished_no_children() -> Self {
        Self::Finished {
            child_join_errors: Vec::new(),
        }
    }
}

#[derive(Clone, Copy, Debug)]
#[must_use]
pub(super) enum HandleSignalResult {
    /// A job control signal was delivered.
    #[cfg(unix)]
    JobControl,

    /// The child was terminated.
    #[cfg_attr(not(windows), expect(dead_code))]
    Terminated(TerminateChildResult),
}

#[derive(Clone, Copy, Debug)]
#[must_use]
pub(super) enum TerminateChildResult {
    /// The child process exited without being forcibly killed.
    Exited,

    /// The child process was forcibly killed.
    Killed,
}
