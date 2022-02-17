# procon-rs

A workspace template for competitive programming (AtCoder) with Rust.

See also: https://zenn.dev/habara_k/scraps/95277a1764d6d8

# Prerequisite

- [cargo-auto-bundle](https://github.com/shino16/cargo-auto-bundle)

# Usage

1. Clone this repository.
2. Write a solution code in src/bin/a.rs
3. Save the library-expanded code to the clipboard with the following command.

```sh
cargo auto-bundle --entry-point src/bin/a.rs --crate external/my-library-rs > tmp.rs && cargo auto-bundle --entry-point tmp.rs --crate external/ac-library-rs | pbcopy
```

=> Submit your code to AtCoder.
