# procon-rs

A workspace template for competitive programming (AtCoder) with Rust.

See also: https://zenn.dev/habara_k/scraps/95277a1764d6d8

# Prerequisite

- [procon-bundler](https://github.com/ngtkana/procon-bundler)

# Usage

1. Clone this repository.
2. Write a solution code in src/bin/a.rs
3. Save the library-expanded code to the clipboard with the following command.

```sh
$ python3 expander.py --crates external/ac-library-rs external/my-library-rs --tgt src/bin/a.rs
```

=> Submit your code to AtCoder.
