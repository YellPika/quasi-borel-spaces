# Quasi-Borel Spaces

This repository contains a formalization of _Quasi-Borel Spaces_[^1] in _Lean 4_[^2].

## Usage

```toml
[[require]]
name = "quasi-borel-spaces"
git = "https://github.com/YellPika/quasi-borel-spaces"
rev = "main"
```

## Differences from the Paper

We differ from the original paper[^1] in the following ways:

- The definition of variable for `Sigma` types (e.g., `(i : I) × P i` or `Σi : I, P i`) is tweaked to more easily support types which are uninhabited.

- A `QuasiBorelSpace` instance is defined for all types `(i : I) × P i` (the paper only allows countable `I`).

- _Probability measures_ from the paper are called `PreProbabilityMeasure`s. We reserve the name `ProbabilityMeasure` for the monad defined in Section V-D[^1], i.e. probability measures quotiented by the relation

  $$
  (α, μ) \sim (β, ν) \iff ∀f\ldotp \int f\ d(α, μ) = \int f\ d(β, ν).
  $$

- We prove the probability measure monad is strong by constructing the strength operation (as in the Isabelle formalization[^3]), instead of by showing `bind` is a morphism (as in Section V-D[^1]).

[^1]: [A Convenient Category for Higher-Order Probability Theory](https://arxiv.org/pdf/1701.02547)
[^2]: https://lean-lang.org/
[^3]: [Quasi_Borel_Spaces - Archive of Formal Proofs](https://www.isa-afp.org/entries/Quasi_Borel_Spaces.html)
