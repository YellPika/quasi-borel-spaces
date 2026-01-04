import Mathlib.Order.OmegaCompletePartialOrder
import Mathlib.Data.Nat.Find
import QuasiBorelSpaces.OmegaCompletePartialOrder.Sum

/-
Faithful ωCPO structure on `Option A` (bottom element `none`, supremum of a
chain given by the first defined element and the ω-supremum of the tail).
-/

variable {A : Type*}

namespace Option

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

instance [LE A] : OrderBot (Option A) where
  bot := none
  bot_le _ := Option.none_le

end Option

namespace OmegaCompletePartialOrder.Chain.Option

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

end OmegaCompletePartialOrder.Chain.Option

namespace OmegaCompletePartialOrder.Option

variable [OmegaCompletePartialOrder A]

noncomputable instance : OmegaCompletePartialOrder (Option A) where
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

variable {B C : Type*} [OmegaCompletePartialOrder B] [OmegaCompletePartialOrder C]

@[fun_prop]
lemma ωScottContinuous_some
    {f : A → B} (hf : ωScottContinuous f)
    : ωScottContinuous fun x ↦ some (f x) := by
  rw [ωScottContinuous_iff_monotone_map_ωSup]
  refine ⟨fun x y hxy ↦ ?_, fun c ↦ ?_⟩
  · simp only [Option.some_le_some]
    apply hf.monotone hxy
  · simp only [hf.map_ωSup, ωSup]
    let c' := c.map {
        toFun := fun x ↦ some (f x)
        monotone' i j hij := by apply hf.monotone hij
    }
    change _ = Option.map ωSup (Chain.Option.sequence c')
    cases hc' : Chain.Option.sequence c' with
    | none =>
      have := Chain.Option.sequence_none c'
      simp only [
        hc', Chain.map_coe, OrderHom.coe_mk, Function.comp_apply,
        reduceCtorEq, forall_const, iff_false, not_true_eq_false, c'] at this
    | some c'' =>
      simp only [Option.map_some, Option.some.injEq]
      have := Chain.Option.sequence_some c' c''
      simp only [
        hc', Chain.map_coe, OrderHom.coe_mk, Function.comp_apply,
        Option.some.injEq, reduceCtorEq, imp_false, not_lt, true_iff, c'] at this
      rcases this with ⟨n, h₁, h₂⟩
      apply le_antisymm
      · simp only [ωSup_le_iff, Chain.map_coe, OrderHom.coe_mk, Function.comp_apply]
        intro i
        apply le_ωSup_of_le i
        rw [←h₁]
        apply hf.monotone
        apply c.monotone
        simp only [le_add_iff_nonneg_left, zero_le]
      · simp only [ωSup_le_iff]
        intro i
        apply le_ωSup_of_le (n + i)
        simp only [← h₁, Chain.map_coe, OrderHom.coe_mk, Function.comp_apply, le_refl]

@[fun_prop]
lemma ωScottContinuous_elim
    [OrderBot C]
    {f : A → Option B} (hf : ωScottContinuous f)
    {g : C} (hg : g = ⊥ := by rfl)
    {h : A → B → C} (hh : ωScottContinuous fun x : A × B ↦ h x.1 x.2)
    : ωScottContinuous fun x ↦ Option.elim (f x) g (h x) := by
  subst hg
  rw [ωScottContinuous_iff_monotone_map_ωSup]
  refine ⟨fun x y hxy ↦ ?_, fun c ↦ ?_⟩
  · cases hfx : f x with
    | none => simp only [hfx, Option.elim_none, bot_le]
    | some z =>
      have := hf.monotone hxy
      cases hgx : f y with
      | none =>
        simp only [hfx, hgx, Option.le_none, reduceCtorEq] at this
      | some w =>
        simp only [hfx, Option.elim_some, hgx]
        refine hh.monotone (⟨?_, ?_⟩ : (x, z) ≤ (y, w))
        · simp only [hxy]
        · simp only [hfx, hgx, Option.some_le_some] at this
          simp only [this]
  · simp only [hf.map_ωSup, ωSup]
    let c' := c.map { toFun := f, monotone' := hf.monotone }
    change (Option.map ωSup (Chain.Option.sequence c')).elim ⊥ (h (ωSup c)) = _
    cases h₁ : Chain.Option.sequence c' with
    | none =>
      have := Chain.Option.sequence_none c'
      simp only [h₁, Chain.map_coe, OrderHom.coe_mk, Function.comp_apply, true_iff, c'] at this
      simp (unfoldPartialApp := true) only [
        Chain, Option.map_none, Option.elim_none, Chain.map,
        OrderHom.comp, Function.comp, OrderHom.coe_mk, this]
      change ⊥ = ωSup (Chain.const ⊥)
      simp only [ωSup_const]
    | some c'' =>
      have := Chain.Option.sequence_some c' c''
      simp only [h₁, Chain.map_coe, OrderHom.coe_mk, Function.comp_apply, true_iff, c'] at this
      rcases this with ⟨n, h₂, h₃⟩
      simp only [Option.map_some, Option.elim_some]
      trans
      · apply hh.map_ωSup (Chain.zip c c'')
      · apply le_antisymm
        · simp only [
            ωSup_le_iff, Chain.map_coe, OrderHom.coe_mk,
            Function.comp_apply, Chain.zip_coe]
          intro i
          apply le_ωSup_of_le (n + i)
          simp only [Chain.map_coe, OrderHom.coe_mk, Function.comp_apply, h₂, Option.elim_some]
          apply hh.monotone (⟨?_, le_rfl⟩ : (c i, c'' i) ≤ (c (n + i), (c'' i)))
          apply c.monotone
          simp only [le_add_iff_nonneg_left, zero_le]
        · simp only [ωSup_le_iff, Chain.map_coe, OrderHom.coe_mk, Function.comp_apply]
          intro i
          by_cases h₄ : i < n
          · simp only [h₃ i h₄, Option.elim_none, bot_le]
          · simp only [not_lt, le_iff_exists_add] at h₄
            rcases h₄ with ⟨i, rfl⟩
            apply le_ωSup_of_le (n + i)
            simp only [
              h₂, Option.elim_some, Chain.map_coe, OrderHom.coe_mk,
              Function.comp_apply, Chain.zip_coe]
            apply hh.monotone (⟨le_rfl, ?_⟩ : (c (n + i), c'' i) ≤ (c (n + i), c'' (n + i)))
            apply c''.monotone
            simp only [le_add_iff_nonneg_left, zero_le]

@[fun_prop]
lemma ωScottContinuous_map
    {f : A → B → C} (hf : ωScottContinuous fun (x, y) ↦ f x y)
    {g : A → Option B} (hg : ωScottContinuous g)
    : ωScottContinuous (fun x ↦ Option.map (f x) (g x)) := by
  have {x} : Option.map (f x) (g x) = Option.elim (g x) .none (.some ∘ f x) := by
    cases g x <;> rfl
  simp only [this]
  apply ωScottContinuous_elim
  · apply hg
  · rfl
  · fun_prop

@[fun_prop]
lemma ωScottContinuous_bind
    {f : A → B → Option C} (hf : ωScottContinuous fun (x, y) ↦ f x y)
    {g : A → Option B} (hg : ωScottContinuous g)
    : ωScottContinuous (fun x ↦ Option.bind (g x) (f x)) := by
  have {x} : Option.bind (g x) (f x) = Option.elim (g x) .none (f x) := by
    cases g x <;> rfl
  simp only [this]
  apply ωScottContinuous_elim
  · apply hg
  · rfl
  · fun_prop

end OmegaCompletePartialOrder.Option
