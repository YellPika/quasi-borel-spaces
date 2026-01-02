import QuasiBorelSpaces.Option
import QuasiBorelSpaces.ENNReal
import QuasiBorelSpaces.OmegaQuasiBorelSpace
import QuasiBorelSpaces.OmegaHom
import QuasiBorelSpaces.FlatReal
import QuasiBorelSpaces.OmegaCompletePartialOrder.Option
import QuasiBorelSpaces.OmegaCompletePartialOrder.Basic
import QuasiBorelSpaces.Basic
import QuasiBorelSpaces.Subtype
import QuasiBorelSpaces.Prop
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Probabilistic powerdomain (sections 4.1–4.4)

This file follows Sections 4.1–4.4 of [VakarKS19].
It records the basic structures (randomizations, expectation operators,
sampling, scoring, closures under ω-sups).
-/

namespace OmegaQuasiBorelSpace

open MeasureTheory
open OmegaCompletePartialOrder
open QuasiBorelSpace

noncomputable section

variable (X : Type*) [OmegaQuasiBorelSpace X]

/-
## Randomizations and expectation operators (Section 4.1)
-/

/-- Randomizations of `X` are partial maps from the randomness source -/
abbrev RX := FlatReal →ω𝒒 Option X

/-- Expectation operators on `X` (the Giry-style exponential) -/
abbrev JX := (X →ω𝒒 ENNReal) →ω𝒒 ENNReal

/-- Lift a weight to a partial result -/
def liftWeight (w : X → ENNReal) : Option X → ENNReal
  | some x => w x
  | none => 0

/-- Domain of a randomization -/
def dom (α : RX X) : Set FlatReal := {r | α r ≠ none}

/-- Evaluate the expectation of a weight under a randomization -/
def E_map (α : RX X) (w : X →ω𝒒 ENNReal) : ENNReal :=
  ∫⁻ r, liftWeight X (fun x => w x) (α r)

/-- Bundle the expectation operator arising from a randomization -/
def E_op (α : RX X) : JX X where
  toFun := fun w => E_map (X := X) α w
  ωScottContinuous' := by
    rw [ωScottContinuous_iff_monotone_map_ωSup]
    refine ⟨fun w1 w2 h ↦ ?_, fun c ↦ ?_⟩
    · simp only [E_map]
      apply lintegral_mono
      intro r
      dsimp [liftWeight]
      cases h_eq : α r with
      | none => apply le_refl
      | some x => exact h x
    · simp only [E_map]
      have h_sup (r)
          : liftWeight X (fun x ↦ (ωSup c) x) (α r)
          = ⨆ n, liftWeight X (fun x => c n x) (α r) := by
        dsimp [liftWeight]
        cases α r with
        | none => simp only [iSup_const]
        | some x => rfl
      conv =>
        lhs
        arg 2
        intro r
        rw [h_sup]
      rw [lintegral_iSup]
      · congr
      · intro n
        have h_eq : (fun r => liftWeight X (fun x => c n x) (α r)) = (fun r =>
        Option.elim (α r) 0 (fun x => c n x)) := by
          ext r
          dsimp [liftWeight, Option.elim]
          cases α r <;> rfl
        rw [h_eq]
        have h_hom : IsHom (fun r => Option.elim (α r) 0 (fun x => c n x)) := by fun_prop
        let f := fun r => Option.elim (α r) 0 (fun x => c n x)
        change Measurable f
        let f' := f ∘ FlatReal.mk
        have h_mk : IsHom FlatReal.mk := isHom_of_measurable (f := FlatReal.mk) (by
          intro s hs
          rcases hs with ⟨t, ht, rfl⟩
          exact ht)
        have : IsHom f' := isHom_comp h_hom h_mk
        have hf' : Measurable f' := measurable_of_isHom _ this
        have h_val : Measurable FlatReal.val := by
          intro s hs
          exact ⟨s, hs, rfl⟩
        rw [show f = f' ∘ FlatReal.val by ext; rfl]
        exact Measurable.comp hf' h_val
      · intro n m hnm r
        dsimp [liftWeight]
        cases α r with
        | none => apply le_refl
        | some x => apply c.monotone hnm
  isHom' := by
    rw [QuasiBorelSpace.isHom_def]
    intro β hβ
    rw [isHom_iff_measurable]
    dsimp

    let F := fun (p : ℝ × FlatReal) => liftWeight X (β p.1) (α p.2)
    change Measurable (fun r => ∫⁻ s, F (r, s) ∂volume)

    apply Measurable.lintegral_prod_right

    have hF_hom : IsHom F := by
      have h_eq : F = (fun (p : ℝ × FlatReal) => Option.elim (α p.2) 0 (fun x => (β p.1) x)) := by
        dsimp [F]
        ext p
        dsimp [liftWeight, Option.elim]
        cases α p.2 <;> rfl
      rw [h_eq]
      apply QuasiBorelSpace.Option.isHom_elim
      · apply isHom_comp α.isHom_coe
        exact Prod.isHom_snd
      · fun_prop
      · have h_uncurry : IsHom (Function.uncurry (fun r x => β r x)) := by
          rw [OmegaQuasiBorelHom.isHom_def] at hβ
          exact hβ
        change IsHom ((Function.uncurry fun r x ↦ (β r) x) ∘ (fun p : (ℝ × FlatReal) × X => (p.1.1, p.2)))
        apply isHom_comp h_uncurry
        apply Prod.isHom_mk
        · apply isHom_comp Prod.isHom_fst
          exact Prod.isHom_fst
        · exact Prod.isHom_snd

    let f' : ℝ × ℝ → ENNReal := F ∘ (Prod.map (id : ℝ → ℝ) FlatReal.mk)
    have h_mk : IsHom FlatReal.mk := isHom_of_measurable (f := FlatReal.mk) (by
      intro s hs
      rcases hs with ⟨t, ht, rfl⟩
      exact ht)
    have h_map : IsHom (Prod.map (id : ℝ → ℝ) FlatReal.mk) := by
      apply Prod.isHom_mk
      · apply isHom_comp isHom_id Prod.isHom_fst
      · apply isHom_comp h_mk Prod.isHom_snd
    have : IsHom f' := isHom_comp hF_hom h_map
    have hf' : Measurable f' := by
      have h_unpack : IsHom (MeasureTheory.unpack (A := ℝ × ℝ)) :=
        isHom_of_measurable _ MeasureTheory.measurable_unpack
      have h_comp : IsHom (f' ∘ MeasureTheory.unpack) := isHom_comp this h_unpack
      have h_meas_comp : Measurable (f' ∘ MeasureTheory.unpack) := measurable_of_isHom _ h_comp
      have h_eq : f' = (f' ∘ MeasureTheory.unpack) ∘ MeasureTheory.pack := by
        ext x; simp only [Function.comp_apply, MeasureTheory.unpack_pack]
      rw [h_eq]
      exact h_meas_comp.comp MeasureTheory.measurable_pack
    have h_val : Measurable FlatReal.val := by
      intro s hs
      exact ⟨s, hs, rfl⟩
    have h_map_val : Measurable (Prod.map (id : ℝ → ℝ) FlatReal.val) := by
      apply Measurable.prodMk
      · apply Measurable.comp measurable_id measurable_fst
      · apply Measurable.comp h_val measurable_snd
    rw [show F = f' ∘ (Prod.map (id : ℝ → ℝ) FlatReal.val) by ext; rfl]
    exact hf'.comp h_map_val

/-- The expectation morphism `E : RX → JX` -/
def E : RX X →ω𝒒 JX X where
  toFun := fun α => E_op (X := X) α
  ωScottContinuous' := by
    rw [ωScottContinuous_iff_monotone_map_ωSup]
    refine ⟨fun x y hxy k ↦ ?_, fun c ↦ ?_⟩
    · simp only [E_op, E_map, liftWeight, OmegaQuasiBorelHom.coe_mk]
      apply lintegral_mono
      intro z
      simp only
      cases hx : x z with
      | none => simp only [zero_le]
      | some xz =>
        cases hy : y z with
        | none =>
          specialize hxy z
          change x z = some xz at hx
          change y z = none at hy
          simp only [hx, hy] at hxy
          cases hxy
        | some yz =>
          simp only
          apply k.monotone_coe
          specialize hxy z
          change x z = some xz at hx
          change y z = some yz at hy
          simp only [hx, hy] at hxy
          apply hxy
    · ext f
      simp only [
        E_op, E_map, liftWeight, ωSup, Chain.Option.sequence, Chain.map_coe,
        Pi.evalOrderHom_coe, OrderHom.coe_mk, Function.comp_apply, Function.eval,
        Chain.Option.project, Option.map_dif, OmegaQuasiBorelHom.coe_mk]
      rw [← MeasureTheory.lintegral_iSup]
      · congr 1
        ext r
        by_cases h : ∃n, (c n r).isSome
        · simp only [h, ↓reduceDIte]
          rw [f.ωScottContinuous_coe.map_ωSup]
          simp only [ωSup, Chain, Chain.map, OrderHom.comp, OrderHom.coe_mk, Function.comp_apply]
          classical
          apply le_antisymm
          · simp only [iSup_le_iff]
            intro i
            apply le_iSup_of_le (Nat.find h + i)
            cases hc : c (Nat.find h + i) r with
            | some x => simp only [Option.getD_some, le_refl]
            | none =>
              have h' := Nat.find_spec h
              rw [Option.isSome_iff_exists] at h'
              have := c.monotone (by grind : Nat.find h ≤ Nat.find h + i) r
              rw [h'.choose_spec, hc, Option.le_none] at this
              contradiction
          · simp only [iSup_le_iff]
            intro i
            apply le_iSup_of_le i
            cases hc : (c i) r with
            | none => simp only [zero_le]
            | some x =>
              apply f.monotone_coe
              have := c.monotone (by grind : i ≤ Nat.find h + i) r
              cases hc' : c (Nat.find h + i) r <;> grind
        · simp only [h, ↓reduceDIte]
          have (n : ℕ) : (c n) r = none := by cases h : (c n) r <;> grind
          simp only [this, ciSup_const]
      · intro n
        change Measurable ((fun r : ℝ ↦ match (c n) ⟨r⟩ with | some x => f x | none => 0) ∘ FlatReal.val)
        apply Measurable.comp
        · apply measurable_of_isHom
          have {r}
              : (match c n ⟨r⟩ with | some x => f x | none => 0)
              = Option.elim (c n ⟨r⟩) 0 f := by
            cases c n ⟨r⟩ <;> rfl
          simp only [this]
          apply Option.isHom_elim
          · apply isHom_comp'
            · fun_prop
            · simp only [isHom_ofMeasurableSpace, measurable_comap_iff]
              apply measurable_id
          · fun_prop
          · fun_prop
        · apply comap_measurable
      · intro i j h r
        cases hc : (c i) r with
        | none => simp only [hc, zero_le]
        | some x =>
          have := c.monotone h r
          simp only [hc, ge_iff_le]
          cases hc' : (c j) r with
          | none => simp only [hc, hc', Option.le_none, reduceCtorEq] at this
          | some y =>
            simp only [hc, hc', Option.some_le_some] at this
            apply f.monotone_coe this
  isHom' := by
    rw [QuasiBorelSpace.isHom_def]
    intro β hβ
    rw [OmegaQuasiBorelHom.isHom_def]
    rw [QuasiBorelSpace.isHom_def]
    intro γ hγ
    rw [isHom_iff_measurable]
    dsimp

    let H := fun (tr : ℝ × FlatReal) => liftWeight X (fun x => (γ tr.1).2 x) (β (γ tr.1).1 tr.2)

    have hH : IsHom H := by
      unfold H liftWeight
      have h_eq : (fun (tr : ℝ × FlatReal) =>
      match β (γ tr.1).1 tr.2 with | some x => (γ tr.1).2 x | none => 0) =
                  (fun tr => Option.elim (β (γ tr.1).1 tr.2) 0 (γ tr.1).2) := by
        ext tr
        cases β (γ tr.1).1 tr.2 <;> simp [Option.elim]
      rw [h_eq]
      apply QuasiBorelSpace.Option.isHom_elim
      · change IsHom ((fun p : (FlatReal →ω𝒒 Option X) × FlatReal =>
          p.1 p.2) ∘ (fun (tr : ℝ × FlatReal) => (β (γ tr.1).1, tr.2)))
        apply isHom_comp (hf := OmegaQuasiBorelHom.isHom_eval)
        apply Prod.isHom_mk
        · apply isHom_comp (hf := hβ)
          apply isHom_comp (hf := Prod.isHom_fst)
          apply isHom_comp (hf := hγ)
          exact Prod.isHom_fst
        · exact Prod.isHom_snd
      · fun_prop
      · change IsHom ((fun p :
        (X →ω𝒒 ENNReal) × X => p.1 p.2) ∘ (fun p : (ℝ × FlatReal) × X => ((γ p.1.1).2, p.2)))
        apply isHom_comp (hf := OmegaQuasiBorelHom.isHom_eval)
        apply Prod.isHom_mk
        · apply isHom_comp (hf := Prod.isHom_snd)
          apply isHom_comp (hf := hγ)
          exact isHom_comp Prod.isHom_fst Prod.isHom_fst
        · exact Prod.isHom_snd

    have hH_meas : Measurable H := by
      let H' : ℝ × ℝ → ENNReal := fun p => H (p.1, FlatReal.mk p.2)
      have hH' : IsHom H' := by
        dsimp [H']
        apply isHom_comp hH
        apply Prod.isHom_mk Prod.isHom_fst
        apply isHom_comp (hf := (isHom_of_measurable FlatReal.mk
        (by intro s hs; rcases hs with ⟨t, ht, rfl⟩; exact ht)))
        exact Prod.isHom_snd

      have hH'_meas : Measurable H' := by
        let f := H' ∘ MeasureTheory.unpack (A := ℝ × ℝ)
        have hf : IsHom f := by
          apply isHom_comp hH'
          apply isHom_of_measurable
          exact MeasureTheory.measurable_unpack
        have hf_meas : Measurable f := by
          rw [← isHom_iff_measurable]
          exact hf
        have h_eq : H' = f ∘ MeasureTheory.pack := by
          ext x
          simp [f, MeasureTheory.unpack_pack]
        rw [h_eq]
        apply Measurable.comp hf_meas
        exact MeasureTheory.measurable_pack

      change Measurable (fun p : ℝ × FlatReal => H' (p.1, p.2.val))
      apply Measurable.comp hH'_meas
      apply Measurable.prodMk measurable_fst
      apply Measurable.comp _ measurable_snd
      intro s hs
      exact ⟨s, hs, rfl⟩

    apply Measurable.lintegral_prod_right hH_meas

/-- Monad unit on randomizations (Dirac) -/
def return_R (x : X) : RX X where
  toFun := fun r => if r.val ∈ Set.Icc 0 1 then some x else none
  ωScottContinuous' := by
    rw [ωScottContinuous_iff_monotone_map_ωSup]
    refine ⟨fun r s hrs ↦ by rw [hrs], fun c ↦ ?_⟩
    let f : FlatReal →o Option X := {
      toFun := fun r => if r.val ∈ Set.Icc 0 1 then some x else none
      monotone' := by
        intro r s hrs
        rw [hrs]
    }
    have h_const : ∀ n, c n = c 0 := fun n => (c.monotone (Nat.zero_le n)).symm
    have h_map : c.map f = Chain.const (f (c 0)) := by
      ext n
      simp [h_const n]
    rw [h_map]
    simp only [ωSup_const]
    congr 1
  isHom' := by
    classical
    change IsHom (fun (r : FlatReal) => if r.val ∈ Set.Icc 0 1 then some x else none)
    apply QuasiBorelSpace.Prop.isHom_ite
    · change IsHom ((fun (v : ℝ) => v ∈ Set.Icc 0 1) ∘ FlatReal.val)
      apply QuasiBorelSpace.isHom_comp
      · rw [isHom_iff_measurable]
        intro s _
        let S : Set ℝ := {v | (v ∈ Set.Icc (0:ℝ) 1) ∈ s}
        have hS : MeasurableSet S := by
          by_cases hT : True ∈ s <;> by_cases hF : False ∈ s
          · suffices S = Set.univ by rw [this]; exact MeasurableSet.univ
            dsimp [S]
            ext v
            simp only [Set.mem_Icc]
            by_cases hv : 0 ≤ v ∧ v ≤ 1
            · simp [hv, hT]
            · simp [hv, hF]
          · suffices S = Set.Icc 0 1 by rw [this]; exact measurableSet_Icc
            dsimp [S]
            ext v
            simp only [Set.mem_Icc]
            by_cases hv : 0 ≤ v ∧ v ≤ 1
            · simp [hv, hT]
            · simp [hv, hF]
          · suffices S = (Set.Icc 0 1)ᶜ by rw [this]; exact MeasurableSet.compl measurableSet_Icc
            dsimp [S]
            ext v
            simp only [Set.mem_Icc]
            by_cases hv : 0 ≤ v ∧ v ≤ 1
            · simp [hv, hT]
            · simp [hv, hF]
          · suffices S = ∅ by rw [this]; exact MeasurableSet.empty
            dsimp [S]
            ext v
            simp only [Set.mem_Icc]
            by_cases hv : 0 ≤ v ∧ v ≤ 1
            · simp [hv, hT]
            · simp [hv, hF]
        exact hS
      · apply isHom_of_measurable
        intro s hs
        exact ⟨s, hs, rfl⟩
    · apply isHom_const
    · apply isHom_const

/-- A measurable splitting of randomness as in the transfer principle -/
class RandomSplit where
  /-- The splitting function -/
  φ : FlatReal → FlatReal × FlatReal
  /-- The splitting function is measurable -/
  measurable_φ : Measurable φ
  /-- Pushing forward Lebesgue along the split yields the product measure -/
  preserves_volume :
    Measure.map φ (volume : Measure FlatReal) =
      (volume : Measure FlatReal).prod (volume : Measure FlatReal)

/-- A default instance of `RandomSplit` (placeholder for now) -/
noncomputable def defaultRandomSplit : RandomSplit := by
  classical
  refine ⟨?φ, ?hφ, ?hpres⟩
  · sorry
  · sorry
  · sorry

attribute [instance] defaultRandomSplit

variable [RandomSplit]

/-- Monad bind on randomizations using the randomness splitting -/
def bind_R {Y} [OmegaQuasiBorelSpace Y] (α : RX X) (k : X → RX Y) : RX Y where
  toFun r :=
    match RandomSplit.φ r with
    | (r₁, r₂) => α r₁ >>= (k · r₂)
  ωScottContinuous' := by
    rw [ωScottContinuous_iff_monotone_map_ωSup]
    refine ⟨fun r s hrs ↦ ?_, fun c ↦ ?_⟩
    · cases hrs
      exact le_rfl
    · have hc : ∀ n, c n = c 0 := fun n => (c.monotone (Nat.zero_le n)).symm
      rw [show ωSup c = c 0 from rfl]
      symm
      let f : FlatReal →o Option Y := {
        toFun := fun r => match RandomSplit.φ r with | (r₁, r₂) => α r₁ >>= (k · r₂)
        monotone' := by
          intro r s hrs
          cases hrs
          exact le_rfl
      }
      change ωSup (c.map f) = f (c 0)
      have : c.map f = Chain.const (f (c 0)) := by
        ext n
        simp [hc]
      rw [this]
      apply ωSup_const
  isHom' := by
    sorry

end

section ExpectationMonad

variable (X : Type*) [OmegaQuasiBorelSpace X]

/-
## Expectation monad (See Section 4.1 of [VakarKS19])
-/

/-- Monad unit on expectation operators -/
def return_J (x : X) : JX X where
  toFun w := w x
  ωScottContinuous' := by
    rw [ωScottContinuous_iff_monotone_map_ωSup]
    exact ⟨fun _ _ hw ↦ hw x, fun c ↦ rfl⟩

/-- Monad bind on expectation operators -/
def bind_J {Y} [OmegaQuasiBorelSpace Y] (μ : JX X) (k : X → JX Y) : JX Y where
  toFun w := μ {
    toFun x := k x w
    isHom' := sorry
    ωScottContinuous' := sorry
  }
  isHom' := sorry
  ωScottContinuous' := sorry

lemma return_bind_J {Y} [OmegaQuasiBorelSpace Y] {x : X} {f : X → JX Y}
    : bind_J _ (return_J _ x) f = f x := by
  apply OmegaQuasiBorelHom.ext
  intro w
  rfl

lemma bind_return_J {Y} [OmegaQuasiBorelSpace Y] {x : JX X}
    : bind_J _ x (return_J _) = x := by
  apply OmegaQuasiBorelHom.ext
  intro w
  rfl

lemma bind_bind_J
    {Y Z} [OmegaQuasiBorelSpace Y] [OmegaQuasiBorelSpace Z]
    {x : JX X} {f : X → JX Y} {g : Y → JX Z}
    : bind_J _ (bind_J _ x f) g = bind_J _ x fun y ↦ bind_J _ (f y) g := by
  apply OmegaQuasiBorelHom.ext
  intro w
  rfl

/-- Expectation preserves the monad structure on randomizations -/
theorem E_preserves_return (x : X) :
    E (X := X) (return_R (X := X) x) = return_J (X := X) x := by
  apply OmegaQuasiBorelHom.ext
  intro w
  change E_map X (return_R X x) w = w x
  unfold E_map return_R
  dsimp [liftWeight]

  let e : FlatReal ≃ᵐ ℝ := {
    toFun := FlatReal.val
    invFun := FlatReal.mk
    left_inv := fun r => rfl
    right_inv := fun y => rfl
    measurable_toFun := Measurable.of_comap_le le_rfl
    measurable_invFun := by
      intro s hs
      rcases hs with ⟨t, ht, rfl⟩
      simpa using ht
  }

  have h_vol_def : (volume : Measure FlatReal) = Measure.map FlatReal.mk volume := rfl
  have h_vol : (volume : Measure FlatReal) = Measure.map e.symm volume := by
    rw [h_vol_def]
    ext s hs
    rw [Measure.map_apply e.symm.measurable hs]
    rw [Measure.map_apply]
    · rfl
    · fun_prop
    · exact hs

  simp [h_vol]
  let g := fun r => liftWeight X (fun x => w x) (return_R X x r)
  have h_eq : ∫⁻ r, g r ∂(Measure.map e.symm volume) = ∫⁻ y, g (e.symm y) ∂volume := by
    exact lintegral_map_equiv g e.symm

  change ∫⁻ r, g r ∂(Measure.map e.symm volume) = w x
  rw [h_eq]
  have h_int : (fun y => g (e.symm y)) =
      (fun y => w x * Set.indicator (Set.Icc 0 1) (fun _ => 1) y) := by
    ext y
    simp only [g, return_R, liftWeight, Set.indicator]
    change (match (if (e.symm y).val ∈ Set.Icc 0 1 then some x else none) with
      | some x => w x | none => 0) = _
    have : (e.symm y).val = y := rfl
    rw [this]
    split_ifs <;> simp
  rw [h_int]
  rw [lintegral_const_mul]
  · rw [lintegral_indicator_const measurableSet_Icc 1]
    rw [Real.volume_Icc]
    simp
  · exact Measurable.indicator measurable_const measurableSet_Icc

theorem E_preserves_bind {Y} [OmegaQuasiBorelSpace Y] (α : RX X) (k : X →ω𝒒 RX Y) :
    E (X := Y) (bind_R (X := X) (Y := Y) α k) =
      bind_J (X := X) (Y := Y) (E (X := X) α) (fun x => E (X := Y) (k x)) := by
  apply OmegaQuasiBorelHom.ext
  intro w
  change E_map Y (bind_R X α k) w = bind_J X (E X α) (fun x => E Y (k x)) w
  unfold bind_J
  dsimp
  unfold E_map
  let f := fun (p : FlatReal × FlatReal) => liftWeight Y w (α p.1 >>= (k · p.2))
  have h_meas_f : Measurable f := by
    let H : ℝ × ℝ → ENNReal := fun p => f (FlatReal.mk p.1, FlatReal.mk p.2)
    have hH : IsHom H := by
      dsimp [H, f]
      change IsHom (fun (p : ℝ × ℝ) => liftWeight Y w (α (FlatReal.mk p.1) >>= (fun x => k x (FlatReal.mk p.2))))
      have h_eq : (fun p => liftWeight Y w (α (FlatReal.mk p.1) >>= (fun x => k x (FlatReal.mk p.2)))) =
                  (fun (p : ℝ × ℝ) =>
                  Option.elim (Option.elim (α (FlatReal.mk p.1)) none (fun x => k x (FlatReal.mk p.2))) 0 w) := by
        ext p
        dsimp [liftWeight, Option.bind, Option.elim]
        cases α (FlatReal.mk p.1) with
        | none => rfl
        | some x =>
          dsimp
          cases (k x) (FlatReal.mk p.2) <;> rfl
      rw [h_eq]
      apply QuasiBorelSpace.Option.isHom_elim
      · apply QuasiBorelSpace.Option.isHom_elim
        · change IsHom (α ∘ FlatReal.mk ∘ Prod.fst)
          apply isHom_comp α.isHom_coe
          apply isHom_comp (isHom_of_measurable (f := FlatReal.mk)
          (by intro s hs; rcases hs with ⟨t, ht, rfl⟩; exact ht))
          exact Prod.isHom_fst
        · fun_prop
        · change IsHom ((fun p : (RX Y) × FlatReal => p.1 p.2) ∘ (fun q : (ℝ × ℝ) × X =>
           (k q.2, FlatReal.mk q.1.2)))
          apply isHom_comp OmegaQuasiBorelHom.isHom_eval
          apply Prod.isHom_mk
          · apply isHom_comp k.isHom_coe
            exact Prod.isHom_snd
          · apply isHom_comp (isHom_of_measurable (f := FlatReal.mk)
            (by intro s hs; rcases hs with ⟨t, ht, rfl⟩; exact ht))
            apply isHom_comp Prod.isHom_snd
            exact Prod.isHom_fst
      · fun_prop
      · change IsHom (w ∘ Prod.snd)
        apply isHom_comp w.isHom_coe
        exact Prod.isHom_snd

    have hH_meas : Measurable H := by
      let F := H ∘ MeasureTheory.unpack (A := ℝ × ℝ)
      have hF : IsHom F := by
        apply isHom_comp hH
        apply isHom_of_measurable
        exact MeasureTheory.measurable_unpack
      have hF_meas : Measurable F := by
        rw [← isHom_iff_measurable]
        exact hF
      have h_eq : H = F ∘ MeasureTheory.pack := by
        ext x
        simp [F, MeasureTheory.unpack_pack]
      rw [h_eq]
      apply Measurable.comp hF_meas
      exact MeasureTheory.measurable_pack

    change Measurable (fun p : FlatReal × FlatReal => H (p.1.val, p.2.val))
    apply Measurable.comp hH_meas
    apply Measurable.prodMk
    · apply Measurable.comp (Measurable.of_comap_le le_rfl) measurable_fst
    · apply Measurable.comp (Measurable.of_comap_le le_rfl) measurable_snd

  have h_lhs : ∫⁻ r, liftWeight Y w (bind_R X α k r) ∂volume = ∫⁻ p, f p ∂(volume.prod volume) := by
    simp only [bind_R]
    change ∫⁻ r, liftWeight Y w (match RandomSplit.φ r with
      | (r₁, r₂) => α r₁ >>= (k · r₂)) ∂volume = _
    have : (fun r => liftWeight Y w (match RandomSplit.φ r with
        | (r₁, r₂) => α r₁ >>= (k · r₂))) = f ∘ RandomSplit.φ := by
      ext r
      simp [f]
      dsimp [RandomSplit.φ, defaultRandomSplit]
    rw [this]
    rw [← RandomSplit.preserves_volume]
    rw [lintegral_map h_meas_f RandomSplit.measurable_φ]
    rfl

  rw [h_lhs]
  have h_fubini : ∫⁻ p, f p ∂(volume.prod volume) =
      ∫⁻ r1, ∫⁻ r2, f (r1, r2) ∂volume ∂volume := lintegral_prod f h_meas_f.aemeasurable
  rw [h_fubini]
  apply lintegral_congr
  intro r1
  simp [f]
  cases h : α r1 with
  | none =>
    simp [liftWeight]
  | some x =>
    simp [liftWeight]
    rfl

/-
## Randomizable operators and ω-closures (See Section 4.2 of [VakarKS19])
-/

/-- Predicate: expectation operator arising from a randomization -/
def Randomizable (μ : JX X) : Prop := ∃ α : RX X, μ = E_op (X := X) α

/-- Randomizable expectation operators as a subtype -/
def SX := {μ : JX X // Randomizable (X := X) μ}
/-- Randomizations valued in randomizations -/
abbrev MRX := FlatReal →ω𝒒 RX X
/-- Randomizable random operators (random elements of `JX`) -/
abbrev MSX := FlatReal →ω𝒒 JX X

/-- Extend `E` pointwise to random randomizations -/
noncomputable def E_rand (β : MRX X) : MSX X where
  toFun r := E_op (X := X) (β r)
  isHom' := by
    have hE : IsHom (fun α => E_op (X := X) α) := (E (X := X)).isHom_coe
    have hβ : IsHom β := β.isHom_coe
    exact isHom_comp hE hβ
  ωScottContinuous' := by
    rw [ωScottContinuous_iff_monotone_map_ωSup]
    refine ⟨fun r s hrs ↦ ?_, fun c ↦ ?_⟩
    · cases hrs
      exact le_rfl
    · let f : OrderHom FlatReal (JX X) :=
        { toFun := fun r => E_op (X := X) (β r)
          monotone' := by
            intro r s hrs
            cases hrs
            exact le_rfl }
      have h_sup : ωSup c = c 0 := rfl
      apply le_antisymm
      · have : f (ωSup c) ≤ ωSup (c.map f) :=
          le_ωSup (c.map f) 0
        simpa [h_sup] using this
      · apply ωSup_le
        intro n
        have hconst : c n = c 0 := by
          have h' : c 0 = c n := c.monotone (Nat.zero_le n)
          exact h'.symm
        simp [h_sup, hconst]

/-- Membership in the ω-sup-closure of randomizable operators -/
inductive InTX : JX X → Prop
  /-- Randomizable operators are in the closure -/
  | randomizable (α : RX X) : InTX (E_op (X := X) α)
  /-- The closure is closed under ω-sups -/
  | sup {c : Chain (JX X)} : (∀ n, InTX (c n)) → InTX (ωSup c)

/-- Membership in the ω-sup-closure of randomizable random operators -/
inductive InMTX : MSX X → Prop
  /-- Randomizable random operators are in the closure -/
  | randomizable (β : MRX X) : InMTX (E_rand (X := X) β)
  /-- The closure is closed under ω-sups -/
  | sup {c : Chain (MSX X)} : (∀ n, InMTX (c n)) → InMTX (ωSup c)

/-- Probabilistic powerdomain: smallest ω-subcpo of `JX` -/
abbrev TX := {μ : JX X // InTX (X := X) μ}

/-- Random elements of the powerdomain -/
abbrev MTX := {β : MSX X // InMTX (X := X) β}

/-- Order structure on `T X` inherited from the ambient `JX` -/
noncomputable instance : PartialOrder (TX X) := inferInstance

/-- Order structure on `M T X` inherited from the ambient `M JX` -/
noncomputable instance : PartialOrder (MTX X) := inferInstance

/- Forgetful inclusions -/
section Inclusions

/-- Inclusion of `TX` into `JX` -/
def TX.incl (t : TX X) : JX X := t.1

/-- Inclusion of `MTX` into `MSX` -/
def MTX.incl (t : MTX X) : MSX X := t.1

end Inclusions

/-- Expectation factors through `T` -/
noncomputable def E_T (α : RX X) : TX X :=
  ⟨E_op (X := X) α, InTX.randomizable α⟩

/-- Pointwise extension of `E_T` to random randomizations -/
noncomputable def E_MT (β : MRX X) : MTX X :=
  ⟨E_rand (X := X) β, InMTX.randomizable β⟩

/-- `TX` inherits an ωCPO structure from `JX` -/
noncomputable instance : OmegaCompletePartialOrder (TX X) :=
{ (inferInstance : PartialOrder (TX X)) with
    ωSup := fun c =>
      let incl : OrderHom (TX X) (JX X) :=
        { toFun := Subtype.val
          monotone' := by
            intro a b h
            exact h }
      ⟨ωSup (c.map incl), InTX.sup (fun n => (c n).2)⟩
    le_ωSup := by
      intro c n
      simpa using (le_ωSup (c.map ⟨Subtype.val, by intro a b h; exact h⟩) n)
    ωSup_le := by
      intro c x hx
      exact (ωSup_le (c := c.map ⟨Subtype.val, by intro a b h; exact h⟩) (x := x.1)
        (by
          intro n
          exact hx n)) }

/-- `TX` is an ωQBS as a full subobject of `JX` -/
noncomputable instance : OmegaQuasiBorelSpace (TX X) :=
{ (inferInstance : OmegaCompletePartialOrder (TX X)),
  (inferInstance : QuasiBorelSpace (TX X)) with
    isHom_ωSup' := by
      intro c hc
      rw [QuasiBorelSpace.Subtype.isHom_def]
      let c' : Chain (ℝ → JX X) := {
        toFun := fun n r => (c n r).val
        monotone' := fun i j h r => c.monotone h r
      }
      have h_eq : (fun r => (ωSup c r).val) = ωSup c' := by
        ext r
        rfl
      rw [h_eq]
      apply OmegaQuasiBorelSpace.isHom_ωSup c'
      intro n
      have hcn := hc n
      rw [QuasiBorelSpace.Subtype.isHom_def] at hcn
      exact hcn }

/-- `MTX` inherits an ωCPO structure from `MSX` -/
noncomputable instance : OmegaCompletePartialOrder (MTX X) :=
{ (inferInstance : PartialOrder (MTX X)) with
    ωSup := fun c =>
      let incl : OrderHom (MTX X) (MSX X) :=
        { toFun := Subtype.val
          monotone' := by
            intro a b h
            exact h }
      ⟨ωSup (c.map incl), InMTX.sup (fun n => (c n).2)⟩
    le_ωSup := by
      intro c n
      simpa using (le_ωSup (c.map ⟨Subtype.val, by intro a b h; exact h⟩) n)
    ωSup_le := by
      intro c x hx
      exact (ωSup_le (c := c.map ⟨Subtype.val, by intro a b h; exact h⟩) (x := x.1)
        (by
          intro n
          exact hx n)) }

/-- `MTX` is an ωQBS as a full subobject of `MSX` -/
noncomputable instance : OmegaQuasiBorelSpace (MTX X) :=
{ (inferInstance : OmegaCompletePartialOrder (MTX X)),
  (inferInstance : QuasiBorelSpace (MTX X)) with
    isHom_ωSup' := by
      intro c hc
      rw [QuasiBorelSpace.Subtype.isHom_def]
      let c' : Chain (ℝ → MSX X) := {
        toFun := fun n r => (c n r).val
        monotone' := fun i j h r => c.monotone h r
      }
      have h_eq : (fun r => (ωSup c r).val) = ωSup c' := by
        ext r
        rfl
      rw [h_eq]
      apply OmegaQuasiBorelSpace.isHom_ωSup c'
      intro n
      have hcn := hc n
      rw [QuasiBorelSpace.Subtype.isHom_def] at hcn
      exact hcn }

/-- Monad unit on `T` obtained by restriction -/
def return_T (x : X) : TX X :=
  ⟨return_J (X := X) x, by
    rw [←E_preserves_return]
    apply InTX.randomizable⟩

/-- Monad bind on `T`, restricting the `J` bind -/
def bind_T {Y} [OmegaQuasiBorelSpace Y] (t : TX X) (k : X → TX Y) : TX Y :=
  ⟨bind_J (X := X) (Y := Y) t.1 (fun x => (k x).1), by
    sorry⟩

/-- (placeholder) The inclusion `T ↪ J` is a monad morphism (See theorem 4.3 of [VakarKS19]) -/
theorem expectation_factorizes_monad :
    True := by
  trivial

/-
## Sampling and conditioning (Section 4.4)
-/

/-- `sample : 1 → R R` is the identity randomization on reals -/
noncomputable def sample_map (_ : Unit) : RX FlatReal where
  toFun := fun r => if r.val ∈ Set.Icc 0 1 then some r else none
  ωScottContinuous' := by
    rw [ωScottContinuous_iff_monotone_map_ωSup]
    refine ⟨fun _ _ h ↦ ?_, fun c ↦ ?_⟩
    · cases h
      rfl
    · have h_eq : ∀ n, c n = c 0 := fun n => (c.monotone (Nat.zero_le n)).symm
      have h_sup : ωSup c = c 0 := rfl
      rw [h_sup]
      let f : FlatReal →o Option FlatReal := {
        toFun := fun r => if r.val ∈ Set.Icc 0 1 then some r else none
        monotone' := by intro r s hrs; cases hrs; rfl
      }
      change f (c 0) = ωSup (c.map f)
      apply le_antisymm
      · exact le_ωSup (c.map f) 0
      · apply ωSup_le
        intro n
        simp only [Chain.map_coe, Function.comp_apply]
        rw [h_eq n]
  isHom' := by
    change IsHom (fun (r : FlatReal) => if r.val ∈ Set.Icc 0 1 then some r else none)
    apply QuasiBorelSpace.Prop.isHom_ite
    · change IsHom ((fun (v : ℝ) => v ∈ Set.Icc 0 1) ∘ FlatReal.val)
      apply QuasiBorelSpace.isHom_comp
      · rw [isHom_iff_measurable]
        intro s _
        by_cases hT : True ∈ s <;> by_cases hF : False ∈ s
        · suffices (fun x => x ∈ Set.Icc (0:ℝ) 1) ⁻¹' s = Set.univ by
            rw [this]; exact MeasurableSet.univ
          ext x; simp; by_cases h : x ∈ Set.Icc (0:ℝ) 1
          · simp only [Set.mem_Icc] at h; rw [eq_true h]; exact hT
          · simp only [Set.mem_Icc] at h; rw [eq_false h]; exact hF
        · suffices (fun x => x ∈ Set.Icc (0:ℝ) 1) ⁻¹' s = Set.Icc 0 1 by
            rw [this]; exact measurableSet_Icc
          ext x; simp; by_cases h : x ∈ Set.Icc (0:ℝ) 1
          · simp only [Set.mem_Icc] at h; rw [eq_true h]; simp [hT]
          · simp only [Set.mem_Icc] at h; rw [eq_false h]; simp [hF]
        · suffices (fun x => x ∈ Set.Icc (0:ℝ) 1) ⁻¹' s = (Set.Icc 0 1)ᶜ by
            rw [this]; exact MeasurableSet.compl measurableSet_Icc
          ext x; simp; by_cases h : x ∈ Set.Icc (0:ℝ) 1
          · simp only [Set.mem_Icc] at h; rw [eq_true h]; simp [hT]; assumption
          · simp only [Set.mem_Icc] at h; rw [eq_false h]; simp [hF]
            intro hx; simp [hx] at h; exact h
        · suffices (fun x => x ∈ Set.Icc (0:ℝ) 1) ⁻¹' s = ∅ by
            rw [this]; exact MeasurableSet.empty
          ext x; simp; by_cases h : x ∈ Set.Icc (0:ℝ) 1
          · simp only [Set.mem_Icc] at h; rw [eq_true h]; exact hT
          · simp only [Set.mem_Icc] at h; rw [eq_false h]; exact hF
      · apply isHom_of_measurable
        exact Measurable.of_comap_le le_rfl
    · apply QuasiBorelSpace.Option.isHom_some isHom_id
    · apply isHom_const

/-- `score : R → R⊥` truncates Lebesgue to an interval of length `|r|` -/
noncomputable def score_map (r : FlatReal) : RX Unit where
  toFun t := if t.val ∈ Set.Icc (0 : ℝ) |r.val| then some () else none
  ωScottContinuous' := by
    rw [ωScottContinuous_iff_monotone_map_ωSup]
    refine ⟨fun _ _ h ↦ ?_, fun c ↦ ?_⟩
    · rw [h]
    · have h_eq : ∀ n, c n = c 0 := fun n => (c.monotone (Nat.zero_le n)).symm
      have h_sup : ωSup c = c 0 := rfl
      rw [h_sup]
      let f : FlatReal →o Option Unit := {
        toFun := fun t => if t.val ∈ Set.Icc 0 |r.val| then some () else none
        monotone' := by intro t1 t2 h; rw [h]
      }
      change f (c 0) = ωSup (c.map f)
      apply le_antisymm
      · exact le_ωSup (c.map f) 0
      · apply ωSup_le
        intro n
        dsimp
        rw [h_eq n]
  isHom' := by
    change IsHom (fun (t : FlatReal) => if t.val ∈ Set.Icc 0 |r.val| then some () else none)
    apply QuasiBorelSpace.Prop.isHom_ite
    · change IsHom ((fun x => x ∈ Set.Icc 0 |r.val|) ∘ FlatReal.val)
      apply QuasiBorelSpace.isHom_comp
      · rw [isHom_iff_measurable]
        intro t _
        by_cases hT : True ∈ t <;> by_cases hF : False ∈ t
        · suffices (fun x => x ∈ Set.Icc 0 |r.val|) ⁻¹' t = Set.univ by
            rw [this]; exact MeasurableSet.univ
          ext x; simp; by_cases h : x ∈ Set.Icc 0 |r.val|
          · simp only [Set.mem_Icc] at h; rw [eq_true h]; exact hT
          · simp only [Set.mem_Icc] at h; rw [eq_false h]; exact hF
        · suffices (fun x => x ∈ Set.Icc 0 |r.val|) ⁻¹' t = Set.Icc 0 |r.val| by
            rw [this]; exact measurableSet_Icc
          ext x; simp; by_cases h : x ∈ Set.Icc 0 |r.val|
          · simp only [Set.mem_Icc] at h; rw [eq_true h]; simp [hT]
          · simp only [Set.mem_Icc] at h; rw [eq_false h]; simp [hF]
        · suffices (fun x => x ∈ Set.Icc 0 |r.val|) ⁻¹' t = (Set.Icc 0 |r.val|)ᶜ by
            rw [this]; exact MeasurableSet.compl measurableSet_Icc
          ext x; simp; by_cases h : x ∈ Set.Icc 0 |r.val|
          · simp only [Set.mem_Icc] at h; rw [eq_true h]; simp [hT]; assumption
          · simp only [Set.mem_Icc] at h; rw [eq_false h]; simp [hF]
            intro hx; simp [hx] at h; exact h
        · suffices (fun x => x ∈ Set.Icc 0 |r.val|) ⁻¹' t = ∅ by
            rw [this]; exact MeasurableSet.empty
          ext x; simp; by_cases h : x ∈ Set.Icc 0 |r.val|
          · simp only [Set.mem_Icc] at h; rw [eq_true h]; exact hT
          · simp only [Set.mem_Icc] at h; rw [eq_false h]; exact hF
      · apply isHom_of_measurable
        exact Measurable.of_comap_le le_rfl
    · apply isHom_const
    · apply isHom_const

/-- Sampling lifted to the powerdomain -/
noncomputable def sample_T (_ : Unit) : TX FlatReal :=
  E_T (X := FlatReal) (sample_map ())

/-- Conditioning lifted to the powerdomain -/
noncomputable def score_T (r : FlatReal) : TX Unit :=
  E_T (X := Unit) (score_map r)

end ExpectationMonad
end OmegaQuasiBorelSpace
