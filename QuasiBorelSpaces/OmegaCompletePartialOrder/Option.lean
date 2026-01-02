import Mathlib.Order.OmegaCompletePartialOrder
import Mathlib.Data.Nat.Find
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

namespace Chain.Option

/--
Given a proof that a `Chain` contains a `some` value, we can construct a `Chain`
that only contains the `some` values.
-/
noncomputable irreducible_def project
    [Preorder A] (c : Chain (Option A)) (h : ∃n, (c n).isSome)
    : Chain A :=
  have : Nonempty A := ⟨Option.get _ (Nat.find_spec h)⟩
  ⟨fun n ↦ (c (Nat.find h + n)).getD this.some, by
    intro i j hij
    dsimp only

    have hhij := c.monotone (by grind : Nat.find h + i ≤ Nat.find h + j)
    have hhi := c.monotone (by grind : Nat.find h ≤ Nat.find h + i)
    have hhj := c.monotone (by grind : Nat.find h ≤ Nat.find h + j)
    have hh := Nat.find_spec h

    cases hi : c (Nat.find h + i) with
    | none =>
      simp only [hi, Option.le_none] at hhi
      simp only [Option.isSome_iff_exists, hhi, Option.isSome_none, Bool.false_eq_true] at hh
    | some x =>

    cases hj : c (Nat.find h + j) with
    | none =>
      simp only [hj, Option.le_none] at hhj
      simp only [Option.isSome_iff_exists, hhj, Option.isSome_none, Bool.false_eq_true] at hh
    | some y =>

    simp only [hi, hj, Option.some_le_some] at hhij
    simp only [Option.getD_some, hhij]⟩

/-- Turns a `Chain` of `Option`s into an equivalent `Option`al `Chain`. -/
noncomputable irreducible_def sequence [Preorder A] (c : Chain (Option A)) : Option (Chain A) :=
  open Classical in
  if h : ∃n, (c n).isSome
  then some (project c h)
  else none

lemma sequence_none [Preorder A] (c : Chain (Option A)) : sequence c = none ↔ ∀n, c n = none := by
  simp only [
    sequence_def, dite_eq_right_iff, reduceCtorEq, imp_false, not_exists,
    Bool.not_eq_true, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none]

lemma sequence_some
    [Preorder A] (c : Chain (Option A)) (c' : Chain A)
    : sequence c = some c' ↔ ∃n, (∀i, c (n + i) = some (c' i)) ∧ (∀i < n, c i = none) := by
  apply Iff.intro
  · intro h₁
    simp only [
      Chain, sequence_def, project_def, Option.dite_none_right_eq_some,
      Option.some.injEq, OrderHom.ext_iff, OrderHom.coe_mk, funext_iff] at h₁
    rcases h₁ with ⟨h₁, h₂⟩
    refine ⟨Nat.find h₁, ?_, ?_⟩
    · intro i
      specialize h₂ i
      have h₃ := Nat.find_spec h₁
      simp only [Option.isSome_iff_exists] at h₃
      have h₄ := c.monotone (by grind : Nat.find h₁ ≤ Nat.find h₁ + i)
      rw [h₃.choose_spec] at h₄
      cases h₅ : c (Nat.find h₁ + i) <;> grind
    · intro i h₂
      have := Nat.find_le (h := h₁) (n := i)
      cases h₃ : c i <;> grind
  · rintro ⟨n, h₁, h₂⟩
    have h₃ : ∃n, (c n).isSome := by
      simp only [Option.isSome_iff_exists]
      use n, c' 0
      grind
    simp only [sequence_def, project_def, h₃, ↓reduceDIte, Option.some.injEq]
    ext i : 2
    simp only [Chain, OrderHom.coe_mk]
    cases h₄ : c (Nat.find h₃ + i) with
    | none =>
      have h₅ := Nat.find_spec h₃
      simp only [Option.isSome_iff_exists] at h₅
      have h₆ := c.monotone (by grind : Nat.find h₃ ≤ Nat.find h₃ + i)
      grind
    | some x =>
      suffices h₅ : Nat.find h₃ = n by
        simp only [h₅, h₁, Option.some.injEq] at h₄
        simp only [Option.getD_some, h₄]
      simp only [Option.isSome_iff_exists, Nat.find_eq_iff, not_exists]
      specialize h₁ 0
      grind

end Chain.Option

noncomputable instance [OmegaCompletePartialOrder A] : OmegaCompletePartialOrder (Option A) where
  ωSup c := Option.map ωSup (Chain.Option.sequence c)
  le_ωSup c i := by
    cases h : Chain.Option.sequence c with
    | none =>
      simp only [Chain.Option.sequence_none] at h
      simp only [h, Option.map_none, le_refl]
    | some c' =>
      simp only [Chain.Option.sequence_some] at h
      rcases h with ⟨n, h₁, h₂⟩
      wlog h₃ : i ≥ n
      · grind
      rw [ge_iff_le, le_iff_exists_add] at h₃
      rcases h₃ with ⟨i, rfl⟩
      simp only [h₁, Option.map_some, Option.some_le_some]
      apply le_ωSup
  ωSup_le c x h := by
    cases h : Chain.Option.sequence c with
    | none =>
      simp only [Chain.Option.sequence_none] at h
      simp only [Option.map_none, Option.none_le]
    | some c' =>
      simp only [Chain.Option.sequence_some] at h
      rcases h with ⟨n, h₁, h₂⟩
      cases x with
      | none =>
        simp only [Option.le_none] at h
        simp only [h, reduceCtorEq, forall_const] at h₁
      | some x =>
        simp only [Option.map_some, Option.some_le_some, ωSup_le_iff]
        grind

end OmegaCompletePartialOrder
