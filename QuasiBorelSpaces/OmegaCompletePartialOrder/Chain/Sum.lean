import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Data.Sum.Order
import Mathlib.Order.OmegaCompletePartialOrder
import Mathlib.Tactic.Have

/-!
# Chain utilities for coproducts of ωCPOs

This file provides utilities for working with chains in sum types,
which are used to construct the ωCPO instance for coproducts.
-/

namespace OmegaCompletePartialOrder.Chain.Sum

variable {A B : Type*}
variable [Preorder A] [Preorder B]

/-- Left injection for chains of sums. -/
def inl (c : Chain A) : Chain (A ⊕ B) :=
  c.map ⟨.inl, by
    intro x y h
    simp only [Sum.inl_le_inl_iff, h]⟩

@[simp]
lemma inl_apply (c : Chain A) (n : ℕ) : inl (B := B) c n = .inl (c n) := rfl

/-- Right injection for chains of sums. -/
def inr (c : Chain B) : Chain (A ⊕ B) :=
  c.map ⟨.inr, by
    intro x y h
    simp only [Sum.inr_le_inr_iff, h]⟩

@[simp]
lemma inr_apply (c : Chain B) (n : ℕ) : inr (A := A) c n = .inr (c n) := rfl

/-- Projects left values out of a chain. -/
@[simps]
def projl [Inhabited A] (c : Chain (A ⊕ B)) : Chain A where
  toFun n := Sum.elim id (fun _ ↦ default) (c n)
  monotone' := by
    refine monotone_nat_of_le_succ fun n ↦ ?_
    have hc := c.monotone (Nat.le_add_right n 1)
    cases hn : c n with
    | inl x =>
      cases hn₁ : c (n + 1) with
      | inl y =>
        simp only [hn, hn₁, Sum.inl_le_inl_iff] at hc
        simp only [Sum.elim_inl, id_eq, hc]
      | inr y => simp only [hn, hn₁, Sum.not_inl_le_inr] at hc
    | inr x =>
      cases hn₁ : c (n + 1) with
      | inl y => simp only [hn, hn₁, Sum.not_inr_le_inl] at hc
      | inr y => simp only [Sum.elim_inr, le_refl]

@[simp]
lemma projl_apply [Inhabited A] (c : Chain (A ⊕ B)) (n : ℕ) :
    projl c n = Sum.elim id (fun _ ↦ default) (c n) :=
  rfl

/-- Projects right values out of a chain. -/
def projr [Inhabited B] (c : Chain (A ⊕ B)) : Chain B :=
  projl (c.map
    ⟨ Sum.swap
    , by
      intro x y h
      cases h with
      | inl h => simp only [Sum.swap_inl, ge_iff_le, Sum.inr_le_inr_iff, h]
      | inr h => simp only [Sum.swap_inr, ge_iff_le, Sum.inl_le_inl_iff, h]
    ⟩)

@[simp]
lemma projr_apply [Inhabited B] (c : Chain (A ⊕ B)) (n : ℕ) :
    projr c n = Sum.elim (fun _ ↦ default) id (c n) := by
  cases h : c n with
  | inl _ =>
      simp only [
        projr, projl_apply, map_coe, OrderHom.coe_mk, Function.comp_apply, h, Sum.swap_inl,
        Sum.elim_inr, Sum.elim_inl]
  | inr _ =>
      simp only [
        projr, projl_apply, map_coe, OrderHom.coe_mk, Function.comp_apply, h, Sum.swap_inr,
        Sum.elim_inl, id_eq, Sum.elim_inr]

/-- Splits a chain of sums into a sum of chains. -/
def distrib (c : Chain (A ⊕ B)) : Chain A ⊕ Chain B :=
  Sum.elim
    (fun d ↦
      let : Inhabited A := ⟨d⟩
      .inl (projl c))
    (fun d ↦
      let : Inhabited B := ⟨d⟩
      .inr (projr c))
    (c 0)

lemma distrib_def [Inhabited A] [Inhabited B] (c : Chain (A ⊕ B))
    : distrib c
    = if (c 0).isLeft then .inl (projl c) else .inr (projr c) := by
  cases hc₀ : c 0 with
  | inl c₀ =>
    simp only [distrib, hc₀, Sum.elim_inl, Sum.isLeft_inl, ↓reduceIte, Sum.inl.injEq]
    ext n
    simp only [projl_apply]
    cases hcₙ : c n with
    | inl cₙ => simp only [Sum.elim_inl, id_eq]
    | inr cₙ =>
      have : c 0 ≤ c n := c.monotone (by simp only [zero_le])
      simp only [hc₀, hcₙ, Sum.not_inl_le_inr] at this
  | inr c₀ =>
    simp only [
      distrib, hc₀, Sum.elim_inr, Sum.isLeft_inr,
      Bool.false_eq_true, ↓reduceIte, Sum.inr.injEq]
    ext n
    simp only [projr_apply]
    cases hcₙ : c n with
    | inl cₙ =>
      have : c 0 ≤ c n := c.monotone (by simp only [zero_le])
      simp only [hc₀, hcₙ, Sum.not_inr_le_inl] at this
    | inr cₙ => simp only [Sum.elim_inr, id_eq]

@[simp]
lemma elim_distrib (c : Chain (A ⊕ B)) : Sum.elim inl inr (distrib c) = c := by
  apply OrderHom.ext
  ext n
  dsimp only [distrib]
  have := c.monotone (zero_le n)
  cases h₀ : c 0 with
  | inl x =>
    cases hₙ : c n with
    | inl y =>
      simp only [h₀, hₙ, Sum.inl_le_inl_iff] at this
      simp only [Sum.elim_inl]
      rw [inl_apply]
      simp only [projl_apply, hₙ, Sum.elim_inl, id_eq]
    | inr y => simp only [h₀, hₙ, Sum.not_inl_le_inr] at this
  | inr x =>
    cases hₙ : c n with
    | inl y => simp only [h₀, hₙ, Sum.not_inr_le_inl] at this
    | inr y =>
      simp only [h₀, hₙ] at this
      simp only [Sum.elim_inr]
      rw [inr_apply]
      simp only [projr_apply, hₙ, Sum.elim_inr, id_eq]

@[simp]
lemma distrib_inl (c : Chain A) : distrib (inl (B := B) c) = .inl c := rfl

@[simp]
lemma distrib_inr (c : Chain B) : distrib (inr (A := A) c) = .inr c := rfl

end OmegaCompletePartialOrder.Chain.Sum
