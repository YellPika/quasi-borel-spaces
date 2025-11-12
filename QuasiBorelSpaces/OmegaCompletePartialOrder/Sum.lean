import Mathlib.Data.Sum.Order
import Mathlib.Order.OmegaCompletePartialOrder
import QuasiBorelSpaces.OmegaCompletePartialOrder.Basic
import QuasiBorelSpaces.OmegaCompletePartialOrder.Chain.Sum

/-!
# ωCPO instance for coproducts

This file provides the `OmegaCompletePartialOrder` instance for `Sum α β`.
-/

namespace OmegaCompletePartialOrder.Sum

universe u v
variable {α : Type u} {β : Type v}
variable [OmegaCompletePartialOrder α] [OmegaCompletePartialOrder β]

@[simps! -isSimp]
noncomputable instance : OmegaCompletePartialOrder (Sum α β) where
  ωSup c := Sum.map ωSup ωSup (Chain.Sum.distrib c)
  le_ωSup c i := by
    classical
    have h := congrArg (fun (f : ℕ →o α ⊕ β) => f i)
      (OmegaCompletePartialOrder.Chain.Sum.elim_distrib c)
    cases hdis : OmegaCompletePartialOrder.Chain.Sum.distrib c with
    | inl cα =>
        have hi : c i = Sum.inl (cα i) := by
          simpa [hdis, OmegaCompletePartialOrder.Chain.Sum.inl_apply] using h.symm
        have hα : cα i ≤ ωSup cα := le_ωSup cα i
        simpa only [hi, Sum.map_inl, ge_iff_le, Sum.inl_le_inl_iff] using hα
    | inr cβ =>
        have hi : c i = Sum.inr (cβ i) := by
          simpa [hdis, OmegaCompletePartialOrder.Chain.Sum.inr_apply] using h.symm
        have hβ : cβ i ≤ ωSup cβ := le_ωSup cβ i
        simpa only [hi, Sum.map_inr, ge_iff_le, Sum.inr_le_inr_iff] using hβ
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
            simp only [Sum.map_inl, ge_iff_le, Sum.inl_le_inl_iff, this]
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
            simp only [Sum.map_inr, ge_iff_le, Sum.inr_le_inr_iff, this]
        | inl a =>
            have hi0 : c 0 = Sum.inr (cβ 0) := by
              simpa [hdis, OmegaCompletePartialOrder.Chain.Sum.inr_apply] using h0.symm
            have hcontr := hx 0
            rw [hi0, hxX] at hcontr
            exact absurd hcontr Sum.not_inr_le_inl

@[simp]
lemma ωSup_inl (c : Chain α) : ωSup (Chain.Sum.inl c : Chain (α ⊕ β)) = .inl (ωSup c) := by
  simp only [ωSup, Chain.Sum.distrib_inl, Sum.map_inl]

@[simp]
lemma ωSup_inr (c : Chain β) : ωSup (Chain.Sum.inr c : Chain (α ⊕ β)) = .inr (ωSup c) := by
  simp only [ωSup, Chain.Sum.distrib_inr, Sum.map_inr]

lemma ωSup_projl [Inhabited α] (c : Chain (α ⊕ β))
    : ωSup (Chain.Sum.projl c)
    = Sum.elim id (fun _ ↦ default) (ωSup c) := by
  cases hc : c 0 with
  | inl c₀ =>
    have : ∀n, ∃a, c n = .inl a := by
      intro n
      have : c 0 ≤ c n := by
        apply c.monotone
        simp only [zero_le]
      simp only [hc] at this
      cases hcₙ : c n with
      | inl cₙ => simp only [Sum.inl.injEq, exists_eq']
      | inr cₙ => simp only [hcₙ, Sum.not_inl_le_inr] at this
    choose x hx using this
    simp only [Chain.Sum.projl, hx, ωSup, Chain.Sum.distrib, Sum.elim_inl, Sum.map_inl, id_eq]
  | inr c₀ =>
    have : ∀n, ∃a, c n = .inr a := by
      intro n
      have : c 0 ≤ c n := by
        apply c.monotone
        simp only [zero_le]
      simp only [hc] at this
      cases hcₙ : c n with
      | inl cₙ => simp only [hcₙ, Sum.not_inr_le_inl] at this
      | inr cₙ => simp only [Sum.inr.injEq, exists_eq']
    choose x hx using this
    simp only [Chain.Sum.projl, hx, ωSup, Chain.Sum.distrib, Sum.elim_inr, Sum.map_inr]
    apply ωSup_const

end OmegaCompletePartialOrder.Sum
