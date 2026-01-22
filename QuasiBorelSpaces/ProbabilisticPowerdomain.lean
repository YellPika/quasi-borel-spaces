import QuasiBorelSpaces.Option
import QuasiBorelSpaces.ENNReal
import QuasiBorelSpaces.OmegaQuasiBorelSpace
import QuasiBorelSpaces.Cont
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
import Mathlib.Probability.Kernel.MeasurableLIntegral

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

variable {X Y : Type*} [OmegaQuasiBorelSpace X] [OmegaQuasiBorelSpace Y]

/-
## Randomizations and expectation operators (Section 4.1)
-/

/-- Randomizations of `X` are partial maps from the randomness source -/
abbrev Randomization (X : Type*) [OmegaQuasiBorelSpace X] := FlatReal →ω𝒒 Option X

namespace Randomization

/-- Domain of a randomization. -/
def dom (α : Randomization X) : Set FlatReal := {r | α r ≠ none}

end Randomization

/-- The expectation morphism `expectation : Randomization → JX`. -/
@[simps]
noncomputable def expectation : Randomization X →ω𝒒 Cont ENNReal X where
  toFun α := {
    apply := {
      toFun := fun w => ∫⁻ r, (α r).elim 0 w
      ωScottContinuous' := by
        apply Measure.ωScottContinuous_lintegral
        · fun_prop (disch := simp only [bot_eq_zero'])
        · intro a
          apply measurable_of_isHom
          fun_prop
    }
  }
  isHom' := by fun_prop
  ωScottContinuous' := by
    apply Cont.ωScottContinuous_mk'
    apply OmegaQuasiBorelHom.ωScottContinuous_mk
    apply Measure.ωScottContinuous_lintegral
    · fun_prop (disch := simp only [bot_eq_zero'])
    · intro a
      apply measurable_of_isHom
      fun_prop

namespace Randomization

/-- Monad unit on randomizations (Dirac) -/
@[simps]
noncomputable def pure (x : X) : Randomization X where
  toFun r := if r.val ∈ Set.Icc 0 1 then some x else none
  isHom' := by apply Prop.isHom_ite <;> fun_prop

end Randomization

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

attribute [fun_prop] RandomSplit.measurable_φ

namespace Randomization

/-- Monad bind on randomizations using the randomness splitting -/
@[simps]
def bind [RandomSplit]
    (α : Randomization X) (k : X →ω𝒒 Randomization Y)
    : Randomization Y where
  toFun r := (α (RandomSplit.φ r).1).bind (k · (RandomSplit.φ r).2)

end Randomization

section ExpectationMonad

variable (X : Type*) [OmegaQuasiBorelSpace X]

/-- Expectation preserves the monad structure on randomizations -/
theorem expectation_preserves_return (x : X) : expectation (.pure x) = .unit x := by
  ext w
  change (expectation (.pure x)).apply w = w x
  simp only [expectation_coe_apply_coe, Randomization.pure_coe, Set.mem_Icc]

  let e : FlatReal ≃ᵐ ℝ := {
    toFun := FlatReal.val
    invFun := FlatReal.mk
    left_inv _ := rfl
    right_inv _ := rfl
    measurable_toFun := Measurable.of_comap_le le_rfl
    measurable_invFun := by simp only [Equiv.coe_fn_symm_mk, FlatReal.R.measurable_mk]
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

  rw [h_vol]
  let g := fun r => (Randomization.pure x r).elim 0 w
  have h_eq : ∫⁻ r, g r ∂(Measure.map e.symm volume) = ∫⁻ y, g (e.symm y) ∂volume := by
    exact lintegral_map_equiv g e.symm

  change ∫⁻ r, g r ∂(Measure.map e.symm volume) = w x
  rw [h_eq]
  have h_int : (fun y => g (e.symm y)) =
      (fun y => w x * Set.indicator (Set.Icc 0 1) (fun _ => 1) y) := by
    ext y
    simp only [g, Randomization.pure, Set.indicator]
    have : (e.symm y).val = y := rfl
    simp only [Set.mem_Icc, OmegaQuasiBorelHom.coe_mk, this, mul_ite, mul_one, mul_zero]
    split_ifs <;> simp only [Option.elim_some, Option.elim_none]
  rw [h_int]
  rw [lintegral_const_mul]
  · rw [lintegral_indicator_const measurableSet_Icc 1]
    rw [Real.volume_Icc]
    simp
  · exact Measurable.indicator measurable_const measurableSet_Icc

theorem expectation_preserves_bind [RandomSplit]
    (α : Randomization X) (k : X →ω𝒒 Randomization Y) :
    expectation (.bind α k) = .bind (expectation.comp k) (expectation α) := by
  ext w
  change (expectation (Randomization.bind α k)).apply w =
    ((expectation α).bind (expectation.comp k)).apply w
  unfold Cont.bind
  dsimp only [
    expectation_coe_apply_coe, Randomization.bind_coe,
    OmegaQuasiBorelHom.coe_mk, OmegaQuasiBorelHom.comp_coe]
  let f := fun (p : FlatReal × FlatReal) ↦ ((α p.1).bind (k · p.2)).elim 0 w
  have h_meas_f : Measurable f := by
    let H : ℝ × ℝ → ENNReal := fun p ↦ f (FlatReal.mk p.1, FlatReal.mk p.2)
    have hH : IsHom H := by
      dsimp [H, f]
      change IsHom (fun p : ℝ × ℝ ↦
        ((α (FlatReal.mk p.1)).bind
        (fun x ↦ k x (FlatReal.mk p.2))).elim 0 w)
      have h_eq : (fun p ↦ ((α (FlatReal.mk p.1)).bind
                           (fun x ↦ k x (FlatReal.mk p.2))).elim 0 w) =
                  (fun (p : ℝ × ℝ) ↦
                    Option.elim
                      (Option.elim (α (FlatReal.mk p.1)) none (fun x => k x (FlatReal.mk p.2)))
                      0
                      w) := by
        ext p
        dsimp only [Option.bind_eq_bind, Option.bind, Option.elim]
        cases α (FlatReal.mk p.1) with
        | none => rfl
        | some x => dsimp only
      rw [h_eq]
      apply QuasiBorelSpace.Option.isHom_elim
      · apply QuasiBorelSpace.Option.isHom_elim
        · change IsHom (α ∘ FlatReal.mk ∘ Prod.fst)
          apply isHom_comp α.isHom_coe
          apply isHom_comp (isHom_of_measurable (f := FlatReal.mk)
          (by intro s hs; rcases hs with ⟨t, ht, rfl⟩; exact ht))
          exact Prod.isHom_fst
        · fun_prop
        · change IsHom ((fun p : (Randomization Y) × FlatReal => p.1 p.2) ∘ (fun q : (ℝ × ℝ) × X =>
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

  have h_lhs :
      ∫⁻ r, (Randomization.bind α k r).elim 0 w ∂volume =
        ∫⁻ p, f p ∂(volume.prod volume) := by
    simp only [Randomization.bind]
    change ∫⁻ r,
      (match RandomSplit.φ r with
       | (r₁, r₂) => (α r₁).bind (k · r₂)).elim 0 w ∂volume = _
    have
        : (fun r => (match RandomSplit.φ r with | (r₁, r₂) => (α r₁).bind (k · r₂)).elim 0 w)
        = f ∘ RandomSplit.φ := by
      ext r
      simp only [Function.comp_apply, f]
    rw [this]
    rw [← RandomSplit.preserves_volume]
    rw [lintegral_map h_meas_f RandomSplit.measurable_φ]
    rfl

  simp only [Randomization.bind_coe] at h_lhs
  rw [h_lhs]
  have h_fubini : ∫⁻ p, f p ∂(volume.prod volume) =
      ∫⁻ r1, ∫⁻ r2, f (r1, r2) ∂volume ∂volume := lintegral_prod f h_meas_f.aemeasurable
  rw [h_fubini]
  apply lintegral_congr
  intro r1
  simp only [f]
  cases h : α r1 with
  | none => simp only [Option.bind_none, Option.elim_none, lintegral_const, zero_mul]
  | some x => simp only [Option.bind_some, Option.elim_some]

-- /-
-- ## Randomizable operators and ω-closures (See Section 4.2 of [VakarKS19])
-- -/

/-- Predicate: expectation operator arising from a randomization -/
def Randomizable (μ : Cont ENNReal X) : Prop := ∃ α : Randomization X, μ = expectation (X := X) α

/-- Randomizable expectation operators as a subtype -/
def RandomizableExpectation := {μ : Cont ENNReal X // Randomizable (X := X) μ}

/-- Random elements of `X` (using `FlatReal` as randomness) -/
abbrev RandomElement (X : Type*) [OmegaQuasiBorelSpace X] := FlatReal →ω𝒒 X

/-- Randomizations valued in randomizations. -/
abbrev RandomizationRandomElement (X : Type*) [OmegaQuasiBorelSpace X] :=
  RandomElement (Randomization X)

/-- Randomizable random operators (random elements of `Cont ENNReal`). -/
abbrev RandomExpectation (X : Type*) [OmegaQuasiBorelSpace X] :=
  RandomElement (Cont ENNReal X)

/-- Extend expectation pointwise to random randomizations. -/
noncomputable def expectationRandom (β : RandomizationRandomElement X) : RandomExpectation X where
  toFun r := expectation (X := X) (β r)

/-- Membership in the ω-sup-closure of randomizable operators -/
inductive InPowerdomain : Cont ENNReal X → Prop
  /-- Randomizable operators are in the closure -/
  | randomizable (α : Randomization X) : InPowerdomain (expectation (X := X) α)
  /-- The closure is closed under ω-sups -/
  | sup {c : Chain (Cont ENNReal X)} : (∀ n, InPowerdomain (c n)) → InPowerdomain (ωSup c)

/-- Membership in the ω-sup-closure of randomizable random operators -/
inductive InRandomPowerdomain : RandomExpectation X → Prop
  /-- Randomizable random operators are in the closure -/
  | randomizable (β : RandomizationRandomElement X) :
      InRandomPowerdomain (expectationRandom (X := X) β)
  /-- The closure is closed under ω-sups -/
  | sup {c : Chain (RandomExpectation X)} :
      (∀ n, InRandomPowerdomain (c n)) → InRandomPowerdomain (ωSup c)

/-- Probabilistic powerdomain: smallest ω-subcpo of `Cont ENNReal` -/
abbrev Powerdomain := {μ : Cont ENNReal X // InPowerdomain (X := X) μ}

/-- Random elements of the powerdomain -/
abbrev RandomPowerdomain := {β : RandomExpectation X // InRandomPowerdomain (X := X) β}

noncomputable instance : QuasiBorelSpace (Powerdomain X) := by
  dsimp only [Powerdomain]
  infer_instance

noncomputable instance : QuasiBorelSpace (RandomPowerdomain X) := by
  dsimp only [RandomPowerdomain]
  infer_instance

/-- Order structure on `Powerdomain X` inherited from the ambient `Cont ENNReal` -/
noncomputable instance : PartialOrder (Powerdomain X) := by
  dsimp [Powerdomain]
  infer_instance

/-- Order structure on `RandomPowerdomain X` inherited from `RandomExpectation`. -/
noncomputable instance : PartialOrder (RandomPowerdomain X) := by
  dsimp [RandomPowerdomain]
  infer_instance

/- Forgetful inclusions -/
section Inclusions

/-- Inclusion of `Powerdomain` into `Cont ENNReal` -/
def Powerdomain.incl (t : Powerdomain X) : Cont ENNReal X := t.1

/-- Inclusion of `RandomPowerdomain` into `RandomExpectation` -/
def RandomPowerdomain.incl (t : RandomPowerdomain X) : RandomExpectation X := t.1

end Inclusions

/-- Expectation factors through `Powerdomain`. -/
noncomputable def expectationPowerdomain (α : Randomization X) : Powerdomain X :=
  ⟨expectation (X := X) α, InPowerdomain.randomizable α⟩

/-- Pointwise extension of `expectationPowerdomain` to random randomizations. -/
noncomputable def expectationRandomPowerdomain (β : RandomizationRandomElement X) :
    RandomPowerdomain X :=
  ⟨expectationRandom (X := X) β, InRandomPowerdomain.randomizable β⟩

/-- `Powerdomain` inherits an ωCPO structure from `Cont ENNReal` -/
noncomputable instance : OmegaCompletePartialOrder (Powerdomain X) :=
  OmegaCompletePartialOrder.subtype _ (by
    intro c hc
    apply InPowerdomain.sup fun n ↦ ?_
    apply hc
    use n)

/-- `Powerdomain` is an ωQBS as a full subobject of `Cont ENNReal` -/
noncomputable instance : OmegaQuasiBorelSpace (Powerdomain X) where
  isHom_ωSup := by
    apply (QuasiBorelSpace.Subtype.isHom_def (f := fun x : Chain (Powerdomain X) => ωSup x)).2
    apply Cont.isHom_mk'
    rw [OmegaQuasiBorelHom.isHom_iff]
    simp only [OmegaQuasiBorelHom.ωSup_coe]
    change IsHom fun x ↦ ωSup _
    apply isHom_ωSup'
    simp only [
      Chain.isHom_iff, Chain.map_coe, Pi.evalOrderHom_coe, OrderHom.coe_mk,
      OrderHom.Subtype.val_coe, Function.comp_apply, Function.eval]
    intro i
    apply isHom_comp'
      (f := fun x : Powerdomain X × (X →ω𝒒 ENNReal) ↦ x.1.val.apply x.2)
      (g := fun x : Chain (Powerdomain X) × (X →ω𝒒 ENNReal) ↦ (x.1 i, x.2))
    · fun_prop
    · apply Prod.isHom_mk
      · apply isHom_comp' (Chain.isHom_apply i) Prod.isHom_fst
      · apply Prod.isHom_snd

/-- the val projection of `TX` is ω-scott continuous -/
@[simp]
lemma Powerdomain.ωScottContinuous_val : ωScottContinuous (fun x : Powerdomain X => x.val) := by
  rw [ωScottContinuous_iff_monotone_map_ωSup]
  refine ⟨fun _ _ h ↦ h, fun _ ↦ rfl⟩

/-- composing with val preserves ω-scott continuity for `Powerdomain` -/
@[fun_prop]
lemma Powerdomain.ωScottContinuous_val' {A : Type*} [OmegaCompletePartialOrder A]
    {f : A → Powerdomain X} (hf : ωScottContinuous f)
    : ωScottContinuous (fun x ↦ (f x).val) :=
  ωScottContinuous.comp (g := fun x : Powerdomain X => x.val) (f := f)
    (Powerdomain.ωScottContinuous_val (X := X)) hf

/-- `RandomPowerdomain` inherits an ωCPO structure from `RandomExpectation` -/
noncomputable instance : OmegaCompletePartialOrder (RandomPowerdomain X) :=
  OmegaCompletePartialOrder.subtype _ (by
    intro c hc
    apply InRandomPowerdomain.sup fun n ↦ ?_
    apply hc
    use n)

/-- `RandomPowerdomain` is an ωQBS as a full subobject of `RandomExpectation` -/
noncomputable instance : OmegaQuasiBorelSpace (RandomPowerdomain X) where
  isHom_ωSup := by
    apply (QuasiBorelSpace.Subtype.isHom_def (f := fun x : Chain (RandomPowerdomain X) => ωSup x)).2
    rw [OmegaQuasiBorelHom.isHom_iff]
    apply Cont.isHom_mk'
    change IsHom fun x ↦ ωSup _
    apply isHom_ωSup'
    simp only [
      Chain.isHom_iff, Chain.map_coe, OrderHom.coe_mk, Pi.evalOrderHom_coe,
      OrderHom.Subtype.val_coe, Function.comp_apply, Function.eval,
      OmegaQuasiBorelHom.isHom_iff]
    intro i
    apply isHom_comp'
      (f := fun x : _ × _ × _ ↦ (x.1.val x.2.1).apply x.2.2)
      (g := fun x : (Chain (RandomPowerdomain X) × FlatReal) × (X →ω𝒒 ENNReal) ↦
        (x.1.1 i, x.1.2, x.2))
    · fun_prop
    · apply Prod.isHom_mk
      · apply isHom_comp' (Chain.isHom_apply i)
        fun_prop
      · fun_prop

namespace Powerdomain

/-- Monad unit on `Powerdomain` obtained by restriction -/
noncomputable def pure (x : X) : Powerdomain X where
  val := Cont.unit x
  property := by
    rw [←expectation_preserves_return (X := X) x]
    apply InPowerdomain.randomizable

/-- Monad bind on `Powerdomain`, restricting the `J` bind -/
noncomputable def bind (t : Powerdomain X) (k : X →ω𝒒 Powerdomain Y) : Powerdomain Y where
  val := t.1.bind {
    toFun x := (k x).1
    isHom' := by
      fun_prop
    ωScottContinuous' := by
      fun_prop
  }
  property := sorry

end Powerdomain

/-- (placeholder) The inclusion `Powerdomain ↪ J` is a monad morphism
(See theorem 4.3 of [VakarKS19]) -/
theorem expectation_factorizes_monad :
    True := by
  trivial

/-
## Sampling and conditioning (Section 4.4)
-/

namespace Randomization

/-- `sample : 1 → R R` is the identity randomization on reals -/
noncomputable def sample : Randomization FlatReal where
  toFun := fun r => if r.val ∈ Set.Icc 0 1 then some r else none
  ωScottContinuous' := by
    fun_prop
  isHom' := by
    change IsHom (fun (r : FlatReal) => if r.val ∈ Set.Icc 0 1 then some r else none)
    apply QuasiBorelSpace.Prop.isHom_ite <;> fun_prop

/-- `score : R → R⊥` truncates Lebesgue to an interval of length `|r|` -/
noncomputable def score (r : FlatReal) : Randomization Unit where
  toFun t := if t.val ∈ Set.Icc (0 : ℝ) |r.val| then some () else none
  ωScottContinuous' := by
    fun_prop
  isHom' := by
    change IsHom (fun (t : FlatReal) => if t.val ∈ Set.Icc 0 |r.val| then some () else none)
    apply QuasiBorelSpace.Prop.isHom_ite <;> fun_prop

end Randomization

namespace Powerdomain

/-- Sampling lifted to the powerdomain -/
noncomputable def sample : Powerdomain FlatReal :=
  expectationPowerdomain (X := FlatReal) Randomization.sample

/-- Conditioning lifted to the powerdomain -/
noncomputable def score (r : FlatReal) : Powerdomain Unit :=
  expectationPowerdomain (X := Unit) (Randomization.score r)

end Powerdomain

end ExpectationMonad
end OmegaQuasiBorelSpace
