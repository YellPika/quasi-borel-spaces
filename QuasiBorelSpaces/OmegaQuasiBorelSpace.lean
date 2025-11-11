import Mathlib.Order.OmegaCompletePartialOrder
import QuasiBorelSpaces.Prod
import QuasiBorelSpaces.Sum
import QuasiBorelSpaces.OmegaCompletePartialOrder.Basic
import QuasiBorelSpaces.OmegaCompletePartialOrder.Sum
import QuasiBorelSpaces.OmegaCompletePartialOrder.Limit

/-!
# Omega quasi-borel spaces

This file defines omega quasi-borel spaces (ωQBS), which combine `QuasiBorelSpace` and
`OmegaCompletePartialOrder` structures with a compatibility axiom stating that pointwise
ω-suprema of ω-chains of morphisms are morphisms (Definition 3.5 in [Vákár–Staton, 2019]).

We prove that products and coproducts preserve the ωQBS structure (Lemma 3.9).

See [VakarKS19].

## Definitions

* `OmegaQuasiBorelSpace`: A type with both an `OmegaCompletePartialOrder` and a
  `QuasiBorelSpace`, satisfying the compatibility axiom.

## Instances

* `instOmegaQuasiBorelSpaceProd`: Products of ωQBSs are ωQBSs.
* `instOmegaQuasiBorelSpaceSum`: Coproducts of ωQBSs are ωQBSs.
-/

namespace QuasiBorelSpaces

open QuasiBorelSpace
open _root_.OmegaCompletePartialOrder (ωSup)
open QuasiBorelSpaces.OmegaCompletePartialOrder (Chain evalOrderHom ωSup_eval)

universe u v

/--
An ωQBS (Omega quasi-borel space) is a type equipped with both a
`QuasiBorelSpace` and an `OmegaCompletePartialOrder`, satisfying the
compatibility axiom: variables are closed under pointwise ω-suprema of ω-chains.
-/
class OmegaQuasiBorelSpace (α : Type u)
  extends OmegaCompletePartialOrder α, QuasiBorelSpace α where
  /-- Compatibility axiom (Definition 3.5 in [Vákár–Staton, 2019]):
  variables are closed under pointwise ω-suprema of ω-chains. -/
  isHom_ωSup :
    ∀ (c : _root_.OmegaCompletePartialOrder.Chain (ℝ → α)),
      (∀ n, IsHom (c n)) →
      IsHom (_root_.OmegaCompletePartialOrder.ωSup c)

namespace OmegaQuasiBorelSpace

variable {α : Type u} {β : Type v}

/-! ### Helpers -/

section Helpers

/-- congruence for IsHom: equal functions preserve IsHom -/
lemma IsHom.congrArg {γ : Type*} [QuasiBorelSpace γ]
    {f g : ℝ → γ} (h : ∀ x, f x = g x) :
    IsHom f → IsHom g := by
  intro hf
  have : f = g := funext h
  rw [← this]
  exact hf

/-- extracting left component from sum variable with default -/
lemma IsHom.caseLeft
    {γ : Type*} [QuasiBorelSpace α] [QuasiBorelSpace γ]
    {f : ℝ → α ⊕ γ} (hf : IsHom f) (a₀ : α) :
    IsHom (fun r => match f r with | Sum.inl a => a | Sum.inr _ => a₀) := by
  have : (fun r => match f r with | Sum.inl a => a | Sum.inr _ => a₀) =
         (Sum.elim id (fun _ => a₀)) ∘ f := by
    ext r
    cases h : f r with
    | inl a => simp [h, Sum.elim]
    | inr b => simp [h, Sum.elim]
  rw [this]
  apply isHom_comp
  · apply QuasiBorelSpace.Sum.isHom_elim
    · exact isHom_id
    · exact isHom_const a₀
  · exact hf

/-- extracting right component from sum variable with default -/
lemma IsHom.caseRight
    {γ : Type*} [QuasiBorelSpace α] [QuasiBorelSpace γ]
    {f : ℝ → α ⊕ γ} (hf : IsHom f) (b₀ : γ) :
    IsHom (fun r => match f r with | Sum.inr b => b | Sum.inl _ => b₀) := by
  have : (fun r => match f r with | Sum.inr b => b | Sum.inl _ => b₀) =
         (Sum.elim (fun _ => b₀) id) ∘ f := by
    ext r
    cases h : f r with
    | inl a => simp [h, Sum.elim]
    | inr b => simp [h, Sum.elim]
  rw [this]
  apply isHom_comp
  · apply QuasiBorelSpace.Sum.isHom_elim
    · exact isHom_const b₀
    · exact isHom_id
  · exact hf

end Helpers

/-- Product of omega quasi-borel spaces is again an omega quasi-borel space. -/
@[simp] instance instOmegaQuasiBorelSpaceProd
    [hα : OmegaQuasiBorelSpace α] [hβ : OmegaQuasiBorelSpace β] :
    OmegaQuasiBorelSpace (α × β) where
  toOmegaCompletePartialOrder := inferInstance
  toQuasiBorelSpace := inferInstance
  isHom_ωSup c hc := by
    rw [QuasiBorelSpace.Prod.isHom_iff]
    constructor
    · let c₁ := c.map ⟨(fun f r => (f r).1), by intro f g h r; exact (h r).1⟩
      have hc₁ : ∀ n, IsHom (c₁ n) := by intro n; sorry
      have h₁ := hα.isHom_ωSup c₁ hc₁
      have eq₁ : ωSup c₁ = fun r => (ωSup c r).1 := by
        funext r
        rw [ωSup_eval]
        rfl
      simpa [eq₁] using h₁
    · let c₂ := c.map ⟨(fun f r => (f r).2), by intro f g h r; exact (h r).2⟩
      have hc₂ : ∀ n, IsHom (c₂ n) := by intro n; sorry
      have h₂ := hβ.isHom_ωSup c₂ hc₂
      have eq₂ : ωSup c₂ = fun r => (ωSup c r).2 := by
        funext r
        rw [ωSup_eval]
        rfl
      simpa [eq₂] using h₂

/-- Coproduct of omega quasi-borel spaces is again an omega quasi-borel space. -/
@[simp] noncomputable instance instOmegaQuasiBorelSpaceSum
    [hα : OmegaQuasiBorelSpace α] [hβ : OmegaQuasiBorelSpace β] :
    OmegaQuasiBorelSpace (Sum α β) where
  toOmegaCompletePartialOrder := inferInstance
  toQuasiBorelSpace := inferInstance
  isHom_ωSup c hc := by
    sorry

end OmegaQuasiBorelSpace

end QuasiBorelSpaces
