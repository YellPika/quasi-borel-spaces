import Mathlib.Order.OmegaCompletePartialOrder
import QuasiBorelSpaces.Basic

open OmegaCompletePartialOrder
open QuasiBorelSpace

/-!
# Omega quasi-Borel spaces

This file defines omega quasi-borel spaces (ωQBS), which combine `QuasiBorelSpace` and
`OmegaCompletePartialOrder` structures with a compatibility axiom stating that pointwise
ω-suprema of ω-chains of morphisms are morphisms (Definition 3.5 in [VakarKS19]).

We prove that products and coproducts preserve the ωQBS structure (Lemma 3.9).

See [VakarKS19].

## Definitions

* `OmegaQuasiBorelSpace`: A type with both an `OmegaCompletePartialOrder` and a
  `QuasiBorelSpace`, satisfying the compatibility axiom.
-/

/--
An ωQBS (Omega quasi-borel space) is a type equipped with both a
`QuasiBorelSpace` and an `OmegaCompletePartialOrder`, satisfying the
compatibility axiom: variables are closed under pointwise ω-suprema of ω-chains.
-/
class OmegaQuasiBorelSpace (A : Type*) extends OmegaCompletePartialOrder A, QuasiBorelSpace A where
  /--
  Compatibility axiom (Definition 3.5 in [VakarKS19]):
  variables are closed under pointwise ω-suprema of ω-chains.
  -/
  isHom_ωSup' (c : Chain (ℝ → A)) :
    (∀ n, IsHom (c n)) →
    IsHom (OmegaCompletePartialOrder.ωSup c)

namespace OmegaQuasiBorelSpace

variable {A B C : Type*}

/--
Pointwise supremum of a chain of QBS morphisms is a QBS morphism
(also known as the "Compatibility Axiom" for the exponential to be an ωQBS)
-/
@[simp, fun_prop]
lemma isHom_ωSup
    [QuasiBorelSpace A] [OmegaQuasiBorelSpace B]
    (c : Chain (A → B)) (hc : ∀ n, IsHom (c n)) :
    IsHom (ωSup c) := by
  rw [QuasiBorelSpace.isHom_def]
  intro α hα
  let c' : Chain (ℝ → B) :=
    { toFun n x := c n (α x)
      monotone' i j h x := c.monotone h (α x) }
  apply isHom_ωSup' c' fun n ↦ ?_
  change IsHom (c n ∘ α)
  fun_prop

instance
    [QuasiBorelSpace A] [OmegaCompletePartialOrder A] [Subsingleton A]
    : OmegaQuasiBorelSpace A where
  isHom_ωSup' := by simp only [isHom_to_subsingleton, implies_true]

end OmegaQuasiBorelSpace
