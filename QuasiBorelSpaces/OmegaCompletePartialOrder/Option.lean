import Mathlib.Order.OmegaCompletePartialOrder
import QuasiBorelSpaces.OmegaCompletePartialOrder.Sum

/-
Faithful ωCPO structure on `Option A` (bottom element `none`, supremum of a
chain given by the first defined element and the ω-supremum of the tail).
-/

namespace OmegaCompletePartialOrder

variable {A : Type*}

instance [Preorder A] : Preorder (Option A) where
  le_refl x := by cases x <;> simp only [Option.le_none, Option.some_le_some, le_refl]
  le_trans x y z h₁ h₂ := by
    cases x <;> cases y <;> cases z <;>
    · simp only [Option.none_le, Option.le_none, reduceCtorEq, Option.some_le_some] at h₁ h₂
      try simp only [Option.some_le_some, Option.none_le, Option.le_none]
      try apply le_trans h₁ h₂
  lt_iff_le_not_ge x y := by
    cases x <;> cases y <;>
    · try simp only [
        Option.none_lt, Option.isSome_some, Option.none_le,
        Option.le_none, reduceCtorEq, not_false_eq_true, and_self,
        Option.not_lt_none, Option.le_none, not_true_eq_false, and_false,
        Option.some_lt_some, Option.some_le_some, lt_iff_le_not_ge]

/-- Bottom-order on options: `none` is bottom, `some` is ordered pointwise. -/
instance [PartialOrder A] : PartialOrder (Option A) where
  le_antisymm x y h₁ h₂ := by cases x <;> cases y <;> grind

noncomputable instance [OmegaCompletePartialOrder A] : OmegaCompletePartialOrder (Option A) where
  ωSup c :=
    open Classical in
    if h : ∃n x, c n = some x
    then some (ωSup ⟨fun n ↦ (c (h.choose + n)).getD h.choose_spec.choose, by
      intro i j h'
      simp only
      have h₁ := c.monotone (by simp : h.choose ≤ h.choose + i)
      have h₂ := c.monotone (by simp : h.choose ≤ h.choose + j)
      rw [h.choose_spec.choose_spec] at h₁ h₂

      cases h₃ : c (h.choose + i) with
      | none => simp only [h₃, Option.le_none, reduceCtorEq] at h₁
      | some x =>

      cases h₄ : c (h.choose + j) with
      | none => simp only [h₄, Option.le_none, reduceCtorEq] at h₂
      | some y =>

      simp only [Option.getD_some, ge_iff_le]
      rw [←Option.some_le_some, ←h₃, ←h₄]
      apply c.monotone
      simp only [add_le_add_iff_left, h']⟩)
    else none
  le_ωSup c i := by
    cases h' : c i with
    | none => simp only [Option.none_le]
    | some x =>
      by_cases h : ∃ n x, c n = some x
      · simp only [h, ↓reduceDIte, Option.some_le_some]
        apply le_ωSup_of_le i
        simp only [Chain, OrderHom.coe_mk]
        have := c.monotone (by simp : i ≤ h.choose + i)
        cases h'' : c (h.choose + i)
        · simp only [h', h'', Option.le_none, reduceCtorEq] at this
        · simp only [h', h'', Option.some_le_some] at this
          simp only [Option.getD_some, this]
      · simp only [h, ↓reduceDIte, Option.le_none]
        simp only [not_exists] at h
        specialize h i
        simp only [h', Option.some.injEq, forall_eq'] at h
  ωSup_le c x h := by
    cases x with
    | none => grind
    | some x =>
      by_cases h' : ∃ n x, c n = some x
      · simp only [Chain, h', ↓reduceDIte, Option.some_le_some, ωSup_le_iff, OrderHom.coe_mk]
        intro i
        cases h'' : c (h'.choose + i) with
        | none =>
          have := c.monotone (by simp : h'.choose ≤ h'.choose + i)
          rw [h'.choose_spec.choose_spec] at this
          simp only [h'', Option.le_none, reduceCtorEq] at this
        | some y =>
          specialize h (h'.choose + i)
          simpa only [Option.getD_some, h'', Option.some_le_some] using h
      · simp only [h', ↓reduceDIte, Option.none_le]

end OmegaCompletePartialOrder
