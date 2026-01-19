# Quasi-Borel Spaces

This repository contains a formalization of _Quasi-Borel Spaces_[^1] and _Quasi-Borel Pre-Domains_[^4] in _Lean 4_[^2].

## Usage

```toml
[[require]]
name = "quasi-borel-spaces"
git = "https://github.com/YellPika/quasi-borel-spaces"
rev = "main"
```

## Differences from the Papers

We differ from the original papers[^1][^4] in the following ways:

- The definition of variable for `Sigma` types (e.g., `(i : I) × P i` or `Σi : I, P i`) is tweaked to more easily support types which are uninhabited.

- A `QuasiBorelSpace` instance is defined for all types `(i : I) × P i` (the paper[^1] only allows countable `I`).

- _Probability measures_ from the paper[^1] are called `PreProbabilityMeasure`s. We reserve the name `ProbabilityMeasure` for the monad defined in Section V-D, i.e. probability measures quotiented by the relation

  $$
  (α, μ) \sim (β, ν) \iff ∀f\ldotp \int f\ d(α, μ) = \int f\ d(β, ν).
  $$

- We prove the probability measure monad is strong by constructing the strength operation (as in the Isabelle formalization[^3]), instead of by showing `bind` is a morphism (as in Section V-D[^1]).

- We provide a `QuasiBorelSpace` instance for `Chain`s, which allows a more succinct definition of `OmegaQuasiBorelSpace`: we only require the supremum function `ωSup : Chain A → A` is a morphism.

[^1]: [A Convenient Category for Higher-Order Probability Theory](https://arxiv.org/pdf/1701.02547)
[^2]: https://lean-lang.org/
[^3]: [Quasi_Borel_Spaces - Archive of Formal Proofs](https://www.isa-afp.org/entries/Quasi_Borel_Spaces.html)
[^4]: [A Domain Theory for Statistical Probabilistic Programming](https://arxiv.org/abs/1811.04196)
