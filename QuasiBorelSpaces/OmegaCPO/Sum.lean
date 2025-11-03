import Mathlib.Data.Sum.Order
import Mathlib.Order.OmegaCompletePartialOrder
import QuasiBorelSpaces.OmegaCPO.Chain.Sum

/-!
# ωCPO instance for coproducts

This file provides the `OmegaCompletePartialOrder` instance for `Sum α β`.
-/

namespace QuasiBorelSpaces.OmegaCPO

open OmegaCompletePartialOrder

universe u v
variable {α : Type u} {β : Type v}
variable [OmegaCompletePartialOrder α] [OmegaCompletePartialOrder β]

/-- ωSup on `α ⊕ β` by splitting a chain of sums into a sum of chains. -/
private noncomputable def ωSupSum (c : Chain (α ⊕ β)) : α ⊕ β :=
  match OmegaCompletePartialOrder.Chain.Sum.distrib c with
  | Sum.inl cα => Sum.inl (ωSup cα)
  | Sum.inr cβ => Sum.inr (ωSup cβ)

noncomputable instance instOmegaCompletePartialOrderSum :
    OmegaCompletePartialOrder (Sum α β) where
  ωSup := ωSupSum
  le_ωSup c i := by
    classical
    have h := congrArg (fun (f : ℕ →o α ⊕ β) => f i)
      (OmegaCompletePartialOrder.Chain.Sum.elim_distrib c)
    cases hdis : OmegaCompletePartialOrder.Chain.Sum.distrib c with
    | inl cα =>
        have hi : c i = Sum.inl (cα i) := by
          simpa [hdis, OmegaCompletePartialOrder.Chain.Sum.inl_apply] using h.symm
        have hα : cα i ≤ ωSup cα := le_ωSup cα i
        simpa [ωSupSum, hdis, hi, Sum.inl_le_inl_iff] using hα
    | inr cβ =>
        have hi : c i = Sum.inr (cβ i) := by
          simpa [hdis, OmegaCompletePartialOrder.Chain.Sum.inr_apply] using h.symm
        have hβ : cβ i ≤ ωSup cβ := le_ωSup cβ i
        simpa [ωSupSum, hdis, hi, Sum.inr_le_inr_iff] using hβ
  ωSup_le c x hx := by
    classical
    have h0 := congrArg (fun (f : ℕ →o α ⊕ β) => f 0)
      (OmegaCompletePartialOrder.Chain.Sum.elim_distrib c)
    cases hdis : OmegaCompletePartialOrder.Chain.Sum.distrib c with
    | inl cα =>
        cases hxX : x with
        | inl a =>
            have hxα : ∀ i, cα i ≤ a := by
              intro i
              have hi : c i = Sum.inl (cα i) := by
                have := congrArg (fun (f : ℕ →o α ⊕ β) => f i)
                  (OmegaCompletePartialOrder.Chain.Sum.elim_distrib c)
                simpa [hdis, OmegaCompletePartialOrder.Chain.Sum.inl_apply] using this.symm
              have hxi := hx i
              rw [hi, hxX] at hxi
              exact Sum.inl_le_inl_iff.mp hxi
            have : ωSup cα ≤ a := ωSup_le _ _ hxα
            simp [ωSupSum, hdis, Sum.inl_le_inl_iff, this]
        | inr b =>
            have hi0 : c 0 = Sum.inl (cα 0) := by
              simpa [hdis, OmegaCompletePartialOrder.Chain.Sum.inl_apply] using h0.symm
            have hcontr := hx 0
            rw [hi0, hxX] at hcontr
            exact absurd hcontr Sum.not_inl_le_inr
    | inr cβ =>
        cases hxX : x with
        | inr b =>
            have hxβ : ∀ i, cβ i ≤ b := by
              intro i
              have hi : c i = Sum.inr (cβ i) := by
                have := congrArg (fun (f : ℕ →o α ⊕ β) => f i)
                  (OmegaCompletePartialOrder.Chain.Sum.elim_distrib c)
                simpa [hdis, OmegaCompletePartialOrder.Chain.Sum.inr_apply] using this.symm
              have hxi := hx i
              rw [hi, hxX] at hxi
              exact Sum.inr_le_inr_iff.mp hxi
            have : ωSup cβ ≤ b := ωSup_le _ _ hxβ
            simp [ωSupSum, hdis, Sum.inr_le_inr_iff, this]
        | inl a =>
            have hi0 : c 0 = Sum.inr (cβ 0) := by
              simpa [hdis, OmegaCompletePartialOrder.Chain.Sum.inr_apply] using h0.symm
            have hcontr := hx 0
            rw [hi0, hxX] at hcontr
            exact absurd hcontr Sum.not_inr_le_inl

end QuasiBorelSpaces.OmegaCPO
