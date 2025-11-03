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

/-- left injection for chains of sums -/
def inl (c : Chain A) : Chain (A ⊕ B) :=
  c.map ⟨_root_.Sum.inl, by
    intro x y h
    simp only [Sum.inl_le_inl_iff, h]⟩

@[simp]
lemma inl_apply (c : Chain A) (n : ℕ) : inl (B := B) c n = _root_.Sum.inl (c n) := rfl

/-- right injection for chains of sums -/
def inr (c : Chain B) : Chain (A ⊕ B) :=
  c.map ⟨_root_.Sum.inr, by
    intro x y h
    simp only [Sum.inr_le_inr_iff, h]⟩

@[simp]
lemma inr_apply (c : Chain B) (n : ℕ) : inr (A := A) c n = _root_.Sum.inr (c n) := rfl

/-- projects left values out of a chain -/
def projl (default : A) (c : Chain (A ⊕ B)) : Chain A where
  toFun n :=
    match c n with
    | _root_.Sum.inl x => x
    | _root_.Sum.inr _ => default
  monotone' := by
    refine monotone_nat_of_le_succ fun n ↦ ?_
    have hc := c.monotone (Nat.le_add_right n 1)
    cases hn : c n with
    | inl x =>
      cases hn₁ : c (n + 1) with
      | inl y =>
        simp only [hn, hn₁, Sum.inl_le_inl_iff] at hc
        simp only [hc]
      | inr y => simp only [hn, hn₁, Sum.not_inl_le_inr] at hc
    | inr x =>
      cases hn₁ : c (n + 1) with
      | inl y => simp only [hn, hn₁, Sum.not_inr_le_inl] at hc
      | inr y => simp only [le_refl]

@[simp]
lemma projl_apply (default : A) (c : Chain (A ⊕ B)) (n : ℕ) :
    projl default c n =
    match c n with
    | _root_.Sum.inl x => x
    | _root_.Sum.inr _ => default := rfl

/-- projects right values out of a chain -/
def projr (default : B) (c : Chain (A ⊕ B)) : Chain B :=
  projl default (c.map
    ⟨ Sum.swap
    , by
      intro x y h
      cases h with
      | inl h => simp only [Sum.swap_inl, ge_iff_le, Sum.inr_le_inr_iff, h]
      | inr h => simp only [Sum.swap_inr, ge_iff_le, Sum.inl_le_inl_iff, h]
    ⟩)

@[simp]
lemma projr_apply (default : B) (c : Chain (A ⊕ B)) (n : ℕ) :
    projr default c n =
    match c n with
    | _root_.Sum.inr x => x
    | _root_.Sum.inl _ => default := by
    cases h : c n with
    | inl _ =>
        simp only [
          projr, projl_apply, map_coe, OrderHom.coe_mk,
          Function.comp_apply, h, Sum.swap_inl
        ]
    | inr _ =>
        simp only [
          projr, projl_apply, map_coe, OrderHom.coe_mk,
          Function.comp_apply, h, Sum.swap_inr
        ]

/-- splits a chain of sums into a sum of chains -/
def distrib (c : Chain (A ⊕ B)) : Chain A ⊕ Chain B :=
  match c 0 with
  | _root_.Sum.inl d => _root_.Sum.inl (projl d c)
  | _root_.Sum.inr d => _root_.Sum.inr (projr d c)

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
      simp only [Sum.elim_inl, inl_apply (projl x c), projl_apply, hₙ]
    | inr y => simp only [h₀, hₙ, Sum.not_inl_le_inr] at this
  | inr x =>
    cases hₙ : c n with
    | inl y => simp only [h₀, hₙ, Sum.not_inr_le_inl] at this
    | inr y =>
      simp only [h₀, hₙ] at this
      simp only [Sum.elim_inr, inr_apply (projr x c), projr_apply, hₙ]

@[simp]
lemma distrib_inl (c : Chain A) : distrib (inl (B := B) c) = _root_.Sum.inl c := rfl

@[simp]
lemma distrib_inr (c : Chain B) : distrib (inr (A := A) c) = _root_.Sum.inr c := rfl

end OmegaCompletePartialOrder.Chain.Sum
