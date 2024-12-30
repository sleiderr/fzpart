# fzpart - A Rust library to interact with GPT / MBR partition tables.

[![Latest Version]][crates.io] [![Documentation]][docs.rs] ![License]

## Features

- **MBR Support**:
  - Read / write a disk Master Boot Record (bootcode and partition table).
  - Interact with the MBR using a raw bytes buffer (useful for bootloaders).

- **GPT Support**:
  - Parse, validate, and modify GUID Partition Tables (GPT).
  - Read and write GPT headers and partition entries.
  - Perform checksum validation and updates for integrity.
  - Manage partitions, including adding, updating, and removing entries.
  - Ensure the consistency of the partition table.

- Supports both `#![no-std]` / `no-alloc` and `std` environments, with almost no loss of functionalities.

## Usage

Add the following to your `Cargo.toml`:

```toml
[dependencies]
fzpart = "0.2.0"
```

## Flags

This crate has the following Cargo features:

- `std` (default): Relies on `std` whenever possible, instead of manual implementations (`std::io` to interact with devices, ...).
                   Also offers a few minor additional methods.
- `alloc` (default): Enables usage of the `alloc` crate, when a global allocator is available. This offers some additional
                     functionalities (partition names conversion, additional consistency checks).

## Contribution

Found a problem or have a suggestion? Feel free to contribute.

Contributions in any form (issues, pull requests, etc.) to this project must
adhere to Rust's [Code of Conduct].

[Code of Conduct]: https://www.rust-lang.org/policies/code-of-conduct

## License

This project is licensed under [GNU GPL, Version 3.0](https://www.gnu.org/licenses/gpl-3.0.en.html)

[crates.io]: https://crates.io/crates/fzpart
[Latest Version]: https://img.shields.io/crates/v/fzpart.svg
[Documentation]: https://docs.rs/fzpart/badge.svg
[docs.rs]: https://docs.rs/fzpart
[License]: https://img.shields.io/crates/l/fzpart.svg
