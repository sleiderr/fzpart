# fzpart - A Rust library to interact with GPT / MBR partition tables.

[![Latest Version]][crates.io] [![Documentation]][docs.rs] ![License]

## Features

- Read / write a disk MBR (bootcode, partition table)
- Interact with the MBR using a raw bytes buffer (useful for bootloaders)

## Usage

Add the following to your `Cargo.toml`:

```toml
[dependencies]
fzpart = "0.0.1"
```

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