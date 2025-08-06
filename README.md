# Veriflex

Veriflex is a verified lexer generator for Lean 4 based on [Brzozowski derivatives](https://en.wikipedia.org/wiki/Brzozowski_derivative) of regular expressions.
Its design is heavily inspired by the paper [Verbatim: A Verified Lexer Generator](https://ieeexplore.ieee.org/document/9474322) by Egolf, Lasser and Fisher.

## Status

This library is still under active development. The computation of Brzozowski derivatives is implemented and fully verified. The lexer using the maximal munch principle is implemented and works, but not yet verified relative to its spec.
Expect major breaking changes before we reach version `1.x`.

## Contributing

Please consult [Contributing.md](CONTRIBUTING.md) for information about how to contribute to the project.