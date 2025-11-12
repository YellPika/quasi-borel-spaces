import Mathlib.Order.OmegaCompletePartialOrder
import QuasiBorelSpaces.OmegaCompletePartialOrder.Chain.Const

/-!
# Basic properties of omega-complete partial orders

This file is a placeholder for lemmas about `OmegaCompletePartialOrder`.
As the library grows, compatibility helpers specific to this project can
be added here.
-/

namespace OmegaCompletePartialOrder

variable {A : Type*} [OmegaCompletePartialOrder A]

@[simp]
lemma ωSup_const (x : A) : ωSup (Chain.const x) = x := by
  apply antisymm (r := (· ≤ ·))
  · simp only [ωSup_le_iff, Chain.const_apply, le_refl, implies_true]
  · apply le_ωSup_of_le 0
    simp only [Chain.const_apply, le_refl]

end OmegaCompletePartialOrder
