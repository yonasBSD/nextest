# Changelog

## [0.12.2] - 2025-02-24

### Added

`RustTestBinaryKind::EXAMPLE` is the string `"example"`.

### Changed

MSRV updated to Rust 1.78.

## [0.12.1] - 2024-09-05

Internal dependency updates.

## [0.12.0] - 2024-08-28

### Changed

- Renamed references from "default-set" to "default-filter" to match cargo-nextest changes.

### Removed

- `NextestExitCode::INVALID_FILTER_EXPRESSION` has been renamed to `INVALID_FILTERSET`.

## [0.11.3] - 2024-08-25

### Changed

- `NextestExitCode::INVALID_FILTER_EXPRESSION` has been renamed to
  `NextestExitCode::INVALID_FILTERSET`. The old name is kept around as a deprecated alias -- it will
  be removed in the next major version.

## [0.11.2] - 2024-08-23

### Added

- New exit code `NO_TESTS_RUN = 4`, indicating no tests to run.
- Support for a new mismatch reason for tests and binaries: that they are not in the default set.

## [0.11.1] - 2024-08-23

This version was not published due to a CI issue.

## [0.11.0] - 2024-05-23

### Added

- `RustBuildMetaSummary` now has a new `platforms` field, which contains information about host and
  target platforms. This field is provided by cargo-nextest 0.9.71 and above.

### Changed

- MSRV updated to Rust 1.73.
- `RustBuildMetaSummary::target_platforms` is now deprecated -- use
  `RustBuildMetaSummary::platforms` if available.

## [0.10.0] - 2023-12-09

### Added

- `RustBuildMetaSummary` has a new field called `build_script_out_dirs`. This is a map of workspace package IDs to their corresponding build script `OUT_DIR`s.

### Misc

- The `.crate` files uploaded to crates.io now contain the `LICENSE-APACHE` and `LICENSE-MIT` license files. Thanks [@musicinmybrain](https://github.com/musicinmybrain) for your first contribution!

## [0.9.3] - 2023-12-03

### Added

- New method `RustBinaryId::from_parts` to construct a `RustBinaryId` from its constituent parts.
- Stabilized and documented [the binary ID format](https://docs.rs/nextest-metadata/latest/nextest_metadata/struct.RustBinaryId.html#method.from_parts).

## [0.9.2] - 2023-09-26

### Added

- New exit code `SETUP_SCRIPT_FAILED`: A setup script failed to execute.

### Changed

- MSRV updated to Rust 1.70.

## [0.9.1] - 2023-07-29

### Added

- New exit codes:
  - `REQUIRED_VERSION_NOT_MET`: The current version of nextest did not meet repository or tool requirements.
  - `RECOMMENDED_VERSION_NOT_MET`: The current version of nextest is older than the minimum recommended version. (This is an advisory code, only generated by `cargo nextest show-config version`).

## [0.9.0] - 2023-06-25

### Changed

- `target-spec` updated to version 3. This version includes support for custom platforms.

## [0.8.2] - 2023-04-08

### Fixed

- `ListCommand` was previously broken: it now uses `--message-format` correctly. Thanks [ Donny/강동윤](https://github.com/kdy1) for your first contribution!

### Changed

- MSRV updated to Rust 1.66.

## [0.8.1] - 2023-04-08

(This was not released due to a publishing issue.)

## [0.8.0] - 2023-01-02

### Added

- A new wrapper for test binary IDs, `RustBinaryId`. This wrapper has a custom `Ord` implementation to ensure that binary IDs are sorted in a reasonable way for `cargo nextest list` output.

### Changed

- Existing uses of test binary IDs have been changed from `String` to `RustBinaryId`.
- MSRV updated to Rust 1.64.

## [0.7.2] - 2022-11-23

### Added

- A new exit code, `DOUBLE_SPAWN_ERROR`, indicates that an error was encountered while attempting to double-spawn a test process.

### Changed

- MSRV updated to Rust 1.62.

## [0.7.1] - 2022-11-23

(This version was not published due to a code issue.)

## [0.7.0] - 2022-10-25

### Added

- `RustBuildMetaSummary` has a new `target-platforms` field, which records information about a list
  of cross-compilation target platforms. This is to prepare for future support for multiple
  `--target` arguments ([#537]).

  This field is optional, which means that the minimum supported nextest version hasn't been bumped
  with this release.

[#537]: https://github.com/nextest-rs/nextest/issues/537

## [0.6.0] - 2022-08-17

### Added

- `RustBuildMetaSummary` has a new `target-platform` field which records the target platform. (This
  field is optional, which means that the minimum supported nextest version hasn't been bumped with
  this release.)

## [0.5.0] - 2022-07-14

(This change was included in 0.4.4, which should have been a breaking change.)

### Changed

- `RustTestSuiteSummary::testcases` renamed to `test_cases`.

## [0.4.4] - 2022-07-13

### Added

- `RustTestSuiteSummary` has a new field `status`, which is a newtype over strings:
  - `"listed"`: the test binary was executed with `--list` to gather the list of tests in it.
  - `"skipped"`: the test binary was not executed because it didn't match any expression filters.

## [0.4.3] - 2022-06-26

### Added

- New documented exit code [`WRITE_OUTPUT_ERROR`].

[`WRITE_OUTPUT_ERROR`]: https://docs.rs/nextest-metadata/latest/nextest_metadata/enum.NextestExitCode.html#associatedconstant.WRITE_OUTPUT_ERROR

## [0.4.2] - 2022-06-13

### Added

- New [documented exit codes] related to self-updates:
  - `UPDATE_ERROR`
  - `UPDATE_AVAILABLE`
  - `UPDATE_DOWNGRADE_NOT_PERFORMED`
  - `UPDATE_CANCELED`
  - `SELF_UPDATE_UNAVAILABLE`

[documented exit codes]: https://docs.rs/nextest-metadata/latest/nextest_metadata/enum.NextestExitCode.html

## [0.4.1] - 2022-06-07

### Added

- New documented exit code [`TEST_LIST_CREATION_FAILED`].

[`TEST_LIST_CREATION_FAILED`]: https://docs.rs/nextest-metadata/latest/nextest_metadata/enum.NextestExitCode.html#associatedconstant.TEST_LIST_CREATION_FAILED

## [0.4.0] - 2022-05-31

### Added

- Support for archiving test binaries:
  - Non-test binaries and dynamic libraries are now recorded to `RustBuildMetaSummary`.

### Changed

- Minimum supported nextest version bumped to 0.9.15.
- MSRV bumped to 1.59.

## [0.3.1] - 2022-04-16

### Added

- New exit code: `INVALID_FILTER_EXPRESSION`.

## [0.3.0] - 2022-03-22

### Added

- `TestListSummary` and `BinaryListSummary` have a new member called `rust_build_meta` key. This key currently contains the target directory, the base output directories, and paths to [search for dynamic libraries in](https://nexte.st/book/env-vars#dynamic-library-paths) relative to the target directory.

### Changed

- MSRV bumped to Rust 1.56.

## [0.2.1] - 2022-03-09

Add documentation about nextest-metadata's "minimum supported cargo-nextest version".

## [0.2.0] - 2022-03-07

Thanks to [Guiguiprim](https://github.com/Guiguiprim) for their contributions to this release!

This release is compatible with cargo-nextest 0.9.10 and later.

### Added

- Lists now contain the `build-platform` variable, introduced in cargo-nextest 0.9.10.
- Support for listing binaries without querying them for the tests they contain.

### Changed

- Fields common to test and binary lists have been factored out into a separate struct, `RustTestBinarySummary`. The struct is marked with `#[serde(flatten)]` so the JSON representation stays the same.

## [0.1.0] - 2022-02-14

- Initial version, with support for listing tests.

[0.12.2]: https://github.com/nextest-rs/nextest/releases/tag/nextest-metadata-0.12.2
[0.12.1]: https://github.com/nextest-rs/nextest/releases/tag/nextest-metadata-0.12.1
[0.12.0]: https://github.com/nextest-rs/nextest/releases/tag/nextest-metadata-0.12.0
[0.11.3]: https://github.com/nextest-rs/nextest/releases/tag/nextest-metadata-0.11.3
[0.11.2]: https://github.com/nextest-rs/nextest/releases/tag/nextest-metadata-0.11.2
[0.11.1]: https://github.com/nextest-rs/nextest/releases/tag/nextest-metadata-0.11.1
[0.11.0]: https://github.com/nextest-rs/nextest/releases/tag/nextest-metadata-0.11.0
[0.10.0]: https://github.com/nextest-rs/nextest/releases/tag/nextest-metadata-0.10.0
[0.9.3]: https://github.com/nextest-rs/nextest/releases/tag/nextest-metadata-0.9.3
[0.9.2]: https://github.com/nextest-rs/nextest/releases/tag/nextest-metadata-0.9.2
[0.9.1]: https://github.com/nextest-rs/nextest/releases/tag/nextest-metadata-0.9.1
[0.9.0]: https://github.com/nextest-rs/nextest/releases/tag/nextest-metadata-0.9.0
[0.8.2]: https://github.com/nextest-rs/nextest/releases/tag/nextest-metadata-0.8.2
[0.8.1]: https://github.com/nextest-rs/nextest/releases/tag/nextest-metadata-0.8.1
[0.8.0]: https://github.com/nextest-rs/nextest/releases/tag/nextest-metadata-0.8.0
[0.7.2]: https://github.com/nextest-rs/nextest/releases/tag/nextest-metadata-0.7.2
[0.7.1]: https://github.com/nextest-rs/nextest/releases/tag/nextest-metadata-0.7.1
[0.7.0]: https://github.com/nextest-rs/nextest/releases/tag/nextest-metadata-0.7.0
[0.6.0]: https://github.com/nextest-rs/nextest/releases/tag/nextest-metadata-0.6.0
[0.5.0]: https://github.com/nextest-rs/nextest/releases/tag/nextest-metadata-0.5.0
[0.4.4]: https://github.com/nextest-rs/nextest/releases/tag/nextest-metadata-0.4.4
[0.4.3]: https://github.com/nextest-rs/nextest/releases/tag/nextest-metadata-0.4.3
[0.4.2]: https://github.com/nextest-rs/nextest/releases/tag/nextest-metadata-0.4.2
[0.4.1]: https://github.com/nextest-rs/nextest/releases/tag/nextest-metadata-0.4.1
[0.4.0]: https://github.com/nextest-rs/nextest/releases/tag/nextest-metadata-0.4.0
[0.3.1]: https://github.com/nextest-rs/nextest/releases/tag/nextest-metadata-0.3.1
[0.3.0]: https://github.com/nextest-rs/nextest/releases/tag/nextest-metadata-0.3.0
[0.2.1]: https://github.com/nextest-rs/nextest/releases/tag/nextest-metadata-0.2.1
[0.2.0]: https://github.com/nextest-rs/nextest/releases/tag/nextest-metadata-0.2.0
[0.1.0]: https://github.com/nextest-rs/nextest/releases/tag/nextest-metadata-0.1.0
