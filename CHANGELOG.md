# Changelog
All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

### Changed
- Use `atomic-polyfill` to support targets without CAS or atomic load/store.

## [0.1.3] - 2022-03-04
### Added
- Added miri test.

### Fixed
- Uncovered by miri: Use `compare_exchange()` instead of
  `compare_exchange_weak()`, because the latter can spuriously fail.

## [0.1.2] - 2021-12-23
### Added
- Top-level documentation.

### Fixed
- Broken example for interrupt handler using `AtomicLazy`.

## [0.1.1] - 2021-12-22
### Added
- Non-blocking methods in order to use `AtomicLazy` from interrupt handlers.

## [0.1.0] - 2021-12-21
- Initial release
