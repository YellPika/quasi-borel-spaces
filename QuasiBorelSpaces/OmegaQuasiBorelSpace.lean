import Mathlib.Order.OmegaCompletePartialOrder
import QuasiBorelSpaces.Bool
import QuasiBorelSpaces.Pi
import QuasiBorelSpaces.Prop
import QuasiBorelSpaces.Prod
import QuasiBorelSpaces.Sum
import QuasiBorelSpaces.OmegaCompletePartialOrder.Basic
import QuasiBorelSpaces.OmegaCompletePartialOrder.Sum
import QuasiBorelSpaces.OmegaCompletePartialOrder.Limit

open OmegaCompletePartialOrder

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
    ∀ (c : Chain (ℝ → α)),
      (∀ n, IsHom (c n)) →
      IsHom (OmegaCompletePartialOrder.ωSup c)

namespace OmegaQuasiBorelSpace

attribute [simp, fun_prop] isHom_ωSup

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
instance instOmegaQuasiBorelSpaceProd
    [hα : OmegaQuasiBorelSpace α] [hβ : OmegaQuasiBorelSpace β] :
    OmegaQuasiBorelSpace (α × β) where
  isHom_ωSup c hc := by
    rw [QuasiBorelSpace.Prod.isHom_iff]
    constructor
    · let c₁ := c.map ⟨(fun f r => (f r).1), by intro f g h r; exact (h r).1⟩
      have hc₁ : ∀ n, IsHom (c₁ n) := by
        intro n
        simpa using QuasiBorelSpace.Prod.isHom_fst_comp (hc n)
      have h₁ := hα.isHom_ωSup c₁ hc₁
      have eq₁ : ωSup c₁ = fun r => (ωSup c r).1 := by
        funext r
        rw [ωSup_eval]
        rfl
      simpa [eq₁] using h₁
    · let c₂ := c.map ⟨(fun f r => (f r).2), by intro f g h r; exact (h r).2⟩
      have hc₂ : ∀ n, IsHom (c₂ n) := by
        intro n
        simpa using QuasiBorelSpace.Prod.isHom_snd_comp (hc n)
      have h₂ := hβ.isHom_ωSup c₂ hc₂
      have eq₂ : ωSup c₂ = fun r => (ωSup c r).2 := by
        funext r
        rw [ωSup_eval]
        rfl
      simpa [eq₂] using h₂

/-- Coproduct of omega quasi-borel spaces is again an omega quasi-borel space. -/
noncomputable instance instOmegaQuasiBorelSpaceSum
    [OmegaQuasiBorelSpace α] [OmegaQuasiBorelSpace β] :
    OmegaQuasiBorelSpace (α ⊕ β) where
  isHom_ωSup c hc := by
    simp only [ωSup]

    wlog hα : Nonempty α
    · have : ∀n r, ∃x, c n r = .inr x := by
        intro n r
        cases c n r with
        | inl x =>
          have : Nonempty α := ⟨x⟩
          contradiction
        | inr x => simp only [Sum.inr.injEq, exists_eq']
      choose x hx using this

      have hx' {a} : Monotone (fun n ↦ x n a) := by
        intro n₁ n₂ hn
        simp only
        suffices Sum.inr (x n₁ a) ≤ (Sum.inr (x n₂ a) : α ⊕ β) by
          simpa only [ge_iff_le, Sum.inr_le_inr_iff] using this
        simp only [← hx]
        apply c.monotone hn

      have hx'' : Monotone x := by
        intro n₁ n₂ hn r
        simp only
        suffices Sum.inr (x n₁ r) ≤ (Sum.inr (x n₂ r) : α ⊕ β) by
          simpa only [ge_iff_le, Sum.inr_le_inr_iff] using this
        simp only [← hx]
        apply c.monotone hn

      have (a : ℝ) : c.map (Pi.evalOrderHom a) = Chain.Sum.inr ⟨fun n ↦ x n a, hx'⟩ := by
        ext n
        simp only [
          Chain.map_coe, Pi.evalOrderHom_coe,
          Function.comp_apply, Function.eval, hx,
          Chain.Sum.inr_apply, Sum.inr.injEq]
        rfl

      simp only [this, Chain.Sum.distrib_inr, Sum.map_inr]
      apply Sum.isHom_inr'
      change IsHom (ωSup ⟨_, hx''⟩)
      apply isHom_ωSup
      intro n
      change IsHom (x n)

      have hα' : IsEmpty α := by simpa only [not_nonempty_iff] using hα
      have : IsHom (fun r ↦ Sum.elim hα'.elim id (c n r)) := by
        apply Sum.isHom_elim'
        · rw [isHom_def]
          intro φ
          have : Nonempty α := ⟨(φ 0).2⟩
          contradiction
        · fun_prop
        · fun_prop

      simp only [hx, Sum.elim_inr, id_eq] at this
      apply this

    wlog hβ : Nonempty β
    · have : ∀n r, ∃x, c n r = .inl x := by
        intro n r
        cases c n r with
        | inr x =>
          have : Nonempty β := ⟨x⟩
          contradiction
        | inl x => simp only [Sum.inl.injEq, exists_eq']
      choose x hx using this

      have hx' {a} : Monotone (fun n ↦ x n a) := by
        intro n₁ n₂ hn
        simp only
        suffices Sum.inl (x n₁ a) ≤ (Sum.inl (x n₂ a) : α ⊕ β) by
          simpa only [ge_iff_le, Sum.inl_le_inl_iff] using this
        simp only [← hx]
        apply c.monotone hn

      have hx'' : Monotone x := by
        intro n₁ n₂ hn r
        simp only
        suffices Sum.inl (x n₁ r) ≤ (Sum.inl (x n₂ r) : α ⊕ β) by
          simpa only [ge_iff_le, Sum.inl_le_inl_iff] using this
        simp only [← hx]
        apply c.monotone hn

      have (a : ℝ) : c.map (Pi.evalOrderHom a) = Chain.Sum.inl ⟨fun n ↦ x n a, hx'⟩ := by
        ext n
        simp only [Chain.map_coe, Pi.evalOrderHom_coe, Function.comp_apply, Function.eval, hx]
        rfl

      simp only [this, Chain.Sum.distrib_inl, Sum.map_inl]
      apply Sum.isHom_inl'
      change IsHom (ωSup ⟨_, hx''⟩)
      apply isHom_ωSup
      intro n
      change IsHom (x n)

      have hβ' : IsEmpty β := by simpa only [not_nonempty_iff] using hβ
      have : IsHom (fun r ↦ Sum.elim id hβ'.elim (c n r)) := by
        apply Sum.isHom_elim'
        · fun_prop
        · rw [isHom_def]
          intro φ
          have : Nonempty β := ⟨(φ 0).2⟩
          contradiction
        · fun_prop

      simp only [hx, Sum.elim_inl, id_eq] at this
      apply this

    have : Inhabited α := ⟨hα.some⟩
    have : Inhabited β := ⟨hβ.some⟩
    simp only [
      Chain.Sum.distrib_def, Chain.map_coe,
      Pi.evalOrderHom_coe, Function.comp_apply, Function.eval]

    simp only [apply_ite, Sum.map_inl, Sum.map_inr]
    apply Prop.isHom_ite
    · apply isHom_cases (f := fun x _ ↦ x = true)
      · fun_prop
      · fun_prop
    · apply Sum.isHom_inl'
      change IsHom (ωSup ⟨_, ?_⟩)
      · apply isHom_ωSup
        intro n
        apply Sum.isHom_elim'
        · fun_prop
        · fun_prop
        · apply hc
      · intro n₁ n₂ hn x
        have : c n₁ x ≤ c n₂ x := c.monotone hn x
        simp only [
          id_eq, Chain.map_coe, Pi.evalOrderHom_coe, Function.comp_apply,
          Function.eval, ge_iff_le]
        cases hcn₁ : c n₁ x with
        | inl cn₁ =>
          cases hcn₂ : c n₂ x with
          | inl hcn₂ => simpa only [hcn₁, hcn₂, Sum.inl_le_inl_iff] using this
          | inr hcn₂ => simp only [hcn₁, hcn₂, Sum.not_inl_le_inr] at this
        | inr cn₁ =>
          cases hcn₂ : c n₂ x with
          | inl hcn₂ => simp only [hcn₁, hcn₂, Sum.not_inr_le_inl] at this
          | inr hcn₂ => simp only [le_refl]
    · apply Sum.isHom_inr'
      change IsHom (ωSup ⟨_, ?_⟩)
      · apply isHom_ωSup
        intro n
        apply Sum.isHom_elim'
        · fun_prop
        · fun_prop
        · apply isHom_comp'
          · apply Sum.isHom_elim'
            · fun_prop
            · fun_prop
            · fun_prop
          · apply hc
      · intro n₁ n₂ hn x
        have : c n₁ x ≤ c n₂ x := c.monotone hn x
        simp only [
          id_eq, Chain.map_coe, Pi.evalOrderHom_coe, Function.comp_apply,
          Function.eval, ge_iff_le]
        cases hcn₁ : c n₁ x with
        | inl cn₁ =>
          cases hcn₂ : c n₂ x with
          | inl hcn₂ => simp only [OrderHom.coe_mk, Sum.swap_inl, le_refl]
          | inr hcn₂ => simp only [hcn₁, hcn₂, Sum.not_inl_le_inr] at this
        | inr cn₁ =>
          cases hcn₂ : c n₂ x with
          | inl hcn₂ => simp only [hcn₁, hcn₂, Sum.not_inr_le_inl] at this
          | inr hcn₂ =>
            simpa only [OrderHom.coe_mk, Sum.swap_inr, hcn₁, hcn₂, Sum.inr_le_inr_iff] using this

end OmegaQuasiBorelSpace

end QuasiBorelSpaces
