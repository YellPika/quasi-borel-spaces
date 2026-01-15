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

noncomputable section

variable {X : Type*} [OmegaQuasiBorelSpace X]

/-
## Randomizations and expectation operators (Section 4.1)
-/

/-- Randomizations of `X` are partial maps from the randomness source -/
abbrev Randomization (X : Type*) [OmegaQuasiBorelSpace X] := FlatReal →ω𝒒 Option X

/-- Bundle the expectation operator arising from a randomization -/
@[simps]
def expectation (α : Randomization X) : Cont ENNReal X where
  apply := {
    toFun w := ∫⁻ r, (α r).elim 0 w
    ωScottContinuous' := by
      apply Measure.ωScottContinuous_lintegral
      · apply Option.ωScottContinuous_elim
        · fun_prop
        · simp only [bot_eq_zero']
        · fun_prop
      · intro a
        apply measurable_of_isHom
        fun_prop
  }

@[simp, fun_prop]
lemma isHom_E_op : IsHom (expectation (X := X)) := by
  unfold expectation
  fun_prop

@[simp, fun_prop]
lemma ωScottContinuous_E_op : ωScottContinuous (expectation (X := X)) := by
  unfold expectation
  apply Cont.ωScottContinuous_mk'
  apply OmegaQuasiBorelHom.ωScottContinuous_mk
  apply Measure.ωScottContinuous_lintegral
  · apply Option.ωScottContinuous_elim
    · fun_prop
    · simp only [bot_eq_zero']
    · fun_prop
  · intro a
    apply measurable_of_isHom
    fun_prop

/-- The expectation morphism `E : RX → JX` -/
@[simps]
def E : Randomization X →ω𝒒 Cont ENNReal X where
  toFun := expectation

/-- Monad unit on randomizations (Dirac) -/
@[simps]
def return_R (x : X) : Randomization X where
  toFun r := if r.val ∈ Set.Icc 0 1 then some x else none
  isHom' := by
    apply Prop.isHom_ite
    · fun_prop
    · fun_prop
    · fun_prop
  ωScottContinuous' := by
    apply ωScottContinuous_ite
    · simp only [FlatReal.le_iff_eq, Set.mem_Icc, eq_iff_iff, forall_eq', implies_true]
    · fun_prop
    · fun_prop

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
def Randomization.bind
    {Y} [OmegaQuasiBorelSpace Y]
    (α : Randomization X) (k : X →ω𝒒 Randomization Y)
    : Randomization Y where
  toFun r := α (RandomSplit.φ r).1 >>= (k · (RandomSplit.φ r).2)
  ωScottContinuous' := by
    simp only [Option.bind_eq_bind]
    fun_prop
  isHom' := by
    simp only [Option.bind_eq_bind]
    fun_prop

end

section ExpectationMonad

variable {X : Type*} [OmegaQuasiBorelSpace X]

/-- Expectation preserves the monad structure on randomizations -/
theorem E_preserves_return (x : X) :
    E (return_R x) = Cont.unit x := by
  ext w
  simp only [E_coe, expectation_apply_coe, return_R_coe, Set.mem_Icc, Cont.unit_coe_apply_coe]

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

  simp only [h_vol]
  let g := fun r => (return_R x r).elim 0 w
  have h_eq : ∫⁻ r, g r ∂(Measure.map e.symm volume) = ∫⁻ y, g (e.symm y) ∂volume := by
    exact lintegral_map_equiv g e.symm

  change ∫⁻ r, g r ∂(Measure.map e.symm volume) = w x
  rw [h_eq]
  have h_int : (fun y => g (e.symm y)) =
      (fun y => w x * Set.indicator (Set.Icc 0 1) (fun _ => 1) y) := by
    ext y
    simp only [g, return_R, Set.indicator]
    have : (e.symm y).val = y := rfl
    simp only [Set.mem_Icc, OmegaQuasiBorelHom.coe_mk, this, mul_ite, mul_one, mul_zero]
    split_ifs <;> simp only [Option.elim_some, Option.elim_none]
  rw [h_int]
  rw [lintegral_const_mul]
  · rw [lintegral_indicator_const measurableSet_Icc 1]
    rw [Real.volume_Icc]
    simp
  · exact Measurable.indicator measurable_const measurableSet_Icc

theorem E_preserves_bind
    {Y} [OmegaQuasiBorelSpace Y]
    (α : Randomization X) (k : X →ω𝒒 Randomization Y)
    : E (Randomization.bind α k) = Cont.bind (E.comp k) (E α) := by
  ext w
  simp only [E_coe, expectation_apply_coe, Cont.bind_coe_coe_apply_coe, OmegaQuasiBorelHom.comp_coe,
    OmegaQuasiBorelHom.coe_mk]
  let f := fun (p : FlatReal × FlatReal) ↦ (α p.1 >>= (k · p.2)).elim 0 w
  have h_meas_f : Measurable f := by
    let H : ℝ × ℝ → ENNReal := fun p ↦ f (FlatReal.mk p.1, FlatReal.mk p.2)
    have hH : IsHom H := by
      dsimp [H, f]
      change IsHom (fun p : ℝ × ℝ ↦
        (α (FlatReal.mk p.1) >>=
        (fun x ↦ k x (FlatReal.mk p.2))).elim 0 w)
      have h_eq : (fun p ↦ (α (FlatReal.mk p.1) >>=
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

  have h_lhs : ∫⁻ r, (Randomization.bind α k r).elim 0 w ∂volume = ∫⁻ p, f p ∂(volume.prod volume) := by
    simp only [Randomization.bind]
    change ∫⁻ r, (match RandomSplit.φ r with | (r₁, r₂) => α r₁ >>= (k · r₂)).elim 0 w ∂volume = _
    have
        : (fun r => (match RandomSplit.φ r with | (r₁, r₂) => α r₁ >>= (k · r₂)).elim 0 w)
        = f ∘ RandomSplit.φ := by
      ext r
      simp only [Option.bind_eq_bind, Function.comp_apply, f]
      dsimp only [defaultRandomSplit, RandomSplit.φ]
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
  simp only [Option.bind_eq_bind, OmegaQuasiBorelHom.coe_mk, f]
  cases h : α r1 with
  | none => simp only [Option.bind_none, Option.elim_none, lintegral_const, zero_mul]
  | some x => simp only [Option.bind_some, Option.elim_some]

-- /-
-- ## Randomizable operators and ω-closures (See Section 4.2 of [VakarKS19])
-- -/

/-- Predicate: expectation operator arising from a randomization -/
def Randomizable (μ : Cont ENNReal X) : Prop := ∃ α : Randomization X, μ = expectation α

/-- Randomizable expectation operators as a subtype -/
def SX := {μ : Cont ENNReal X // Randomizable μ}
/-- Randomizations valued in randomizations -/
abbrev MRX (X : Type*) [OmegaQuasiBorelSpace X] := FlatReal →ω𝒒 Randomization X
/-- Randomizable random operators (random elements of `Cont ENNReal`) -/
abbrev MSX (X : Type*) [OmegaQuasiBorelSpace X] := FlatReal →ω𝒒 Cont ENNReal X

/-- Extend `E` pointwise to random randomizations -/
noncomputable def E_rand (β : MRX X) : MSX X where
  toFun r := expectation (β r)
  isHom' := by
    have hE : IsHom (fun α => expectation α) := (E (X := X)).isHom_coe
    have hβ : IsHom β := β.isHom_coe
    exact isHom_comp hE hβ
  ωScottContinuous' := by
    rw [ωScottContinuous_iff_monotone_map_ωSup]
    refine ⟨fun r s hrs ↦ ?_, fun c ↦ ?_⟩
    · cases hrs
      exact le_rfl
    · let f : OrderHom FlatReal (Cont ENNReal X) :=
        { toFun := fun r => expectation (β r)
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
inductive InTX : Cont ENNReal X → Prop
  /-- Randomizable operators are in the closure -/
  | randomizable (α : Randomization X) : InTX (expectation (X := X) α)
  /-- The closure is closed under ω-sups -/
  | sup {c : Chain (Cont ENNReal X)} : (∀ n, InTX (c n)) → InTX (ωSup c)

/-- Membership in the ω-sup-closure of randomizable random operators -/
inductive InMTX : MSX X → Prop
  /-- Randomizable random operators are in the closure -/
  | randomizable (β : MRX X) : InMTX (E_rand (X := X) β)
  /-- The closure is closed under ω-sups -/
  | sup {c : Chain (MSX X)} : (∀ n, InMTX (c n)) → InMTX (ωSup c)

/-- Probabilistic powerdomain: smallest ω-subcpo of `Cont ENNReal` -/
abbrev TX (X : Type*) [OmegaQuasiBorelSpace X] := {μ : Cont ENNReal X // InTX (X := X) μ}

/-- Random elements of the powerdomain -/
abbrev MTX (X : Type*) [OmegaQuasiBorelSpace X] := {β : MSX X // InMTX (X := X) β}

/-- Order structure on `T X` inherited from the ambient `Cont ENNReal` -/
noncomputable instance : PartialOrder (TX X) := inferInstance

/-- Order structure on `M T X` inherited from the ambient `M (Cont ENNReal)` -/
noncomputable instance : PartialOrder (MTX X) := inferInstance

/- Forgetful inclusions -/
section Inclusions

/-- Inclusion of `TX` into `Cont ENNReal` -/
def TX.incl (t : TX X) : Cont ENNReal X := t.1

/-- Inclusion of `MTX` into `MSX` -/
def MTX.incl (t : MTX X) : MSX X := t.1

end Inclusions

/-- Expectation factors through `T` -/
noncomputable def E_T (α : Randomization X) : TX X :=
  ⟨expectation (X := X) α, InTX.randomizable α⟩

/-- Pointwise extension of `E_T` to random randomizations -/
noncomputable def E_MT (β : MRX X) : MTX X :=
  ⟨E_rand (X := X) β, InMTX.randomizable β⟩

/-- `TX` inherits an ωCPO structure from `Cont ENNReal` -/
noncomputable instance : OmegaCompletePartialOrder (TX X) :=
  OmegaCompletePartialOrder.subtype _ (by
    intro c hc
    apply InTX.sup fun n ↦ ?_
    apply hc
    use n)

/-- `TX` is an ωQBS as a full subobject of `Cont ENNReal` -/
noncomputable instance : OmegaQuasiBorelSpace (TX X) where
  isHom_ωSup := by
    simp only [Subtype.isHom_def]
    apply Cont.isHom_mk'
    simp only [OmegaQuasiBorelHom.isHom_iff, OmegaQuasiBorelHom.ωSup_coe]
    change IsHom fun x ↦ ωSup _
    apply isHom_ωSup'
    simp only [
      Chain.isHom_iff, Chain.map_coe, Pi.evalOrderHom_coe, OrderHom.coe_mk,
      OrderHom.Subtype.val_coe, Function.comp_apply, Function.eval]
    intro i
    apply isHom_comp'
      (f := fun x : TX X × (X →ω𝒒 ENNReal) ↦ x.1.val.apply x.2)
      (g := fun x : Chain (TX X) × (X →ω𝒒 ENNReal) ↦ (x.1 i, x.2))
    · fun_prop
    · apply Prod.isHom_mk
      · apply isHom_comp' (Chain.isHom_apply i) Prod.isHom_fst
      · apply Prod.isHom_snd

/-- the val projection of `TX` is ω-scott continuous -/
@[simp]
lemma TX.ωScottContinuous_val : ωScottContinuous (Subtype.val (p := InTX (X := X))) := by
  rw [ωScottContinuous_iff_monotone_map_ωSup]
  refine ⟨fun _ _ h ↦ h, fun _ ↦ rfl⟩

/-- composing with val preserves ω-scott continuity for `TX` -/
@[fun_prop]
lemma TX.ωScottContinuous_val' {A : Type*} [OmegaCompletePartialOrder A]
    {f : A → TX X} (hf : ωScottContinuous f)
    : ωScottContinuous (fun x ↦ (f x).val) :=
  ωScottContinuous.comp (TX.ωScottContinuous_val (X := X)) hf

/-- `MTX` inherits an ωCPO structure from `MSX` -/
noncomputable instance : OmegaCompletePartialOrder (MTX X) :=
  OmegaCompletePartialOrder.subtype _ (by
    intro c hc
    apply InMTX.sup fun n ↦ ?_
    apply hc
    use n)

/-- `MTX` is an ωQBS as a full subobject of `MSX` -/
noncomputable instance : OmegaQuasiBorelSpace (MTX X) where
  isHom_ωSup := by
    simp only [Subtype.isHom_def, OmegaQuasiBorelHom.isHom_iff]
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
      (g := fun x : (Chain (MTX X) × FlatReal) × (X →ω𝒒 ENNReal) ↦ (x.1.1 i, x.1.2, x.2))
    · fun_prop
    · apply Prod.isHom_mk
      · apply isHom_comp' (Chain.isHom_apply i)
        fun_prop
      · fun_prop

/-- Monad unit on `T` obtained by restriction -/
noncomputable def return_T (x : X) : TX X where
  val := Cont.unit x
  property := by
    rw [←E_preserves_return]
    apply InTX.randomizable

/-- Monad bind on `T`, restricting the `J` bind -/
noncomputable def bind_T {Y} [OmegaQuasiBorelSpace Y] (t : TX X) (k : X →ω𝒒 TX Y) : TX Y where
  val := t.1.bind {
    toFun x := (k x).1
    ωScottContinuous' := by fun_prop
  }
  property := sorry

/-- (placeholder) The inclusion `T ↪ J` is a monad morphism (See theorem 4.3 of [VakarKS19]) -/
theorem expectation_factorizes_monad :
    True := by
  trivial

/-
## Sampling and conditioning (Section 4.4)
-/

/-- `sample : 1 → R R` is the identity randomization on reals -/
noncomputable def sample_map (_ : Unit) : Randomization FlatReal where
  toFun := fun r => if r.val ∈ Set.Icc 0 1 then some r else none
  ωScottContinuous' := by fun_prop
  isHom' := by
    apply Prop.isHom_ite
    · fun_prop
    · fun_prop
    · fun_prop

/-- `score : R → R⊥` truncates Lebesgue to an interval of length `|r|` -/
noncomputable def score_map (r : FlatReal) : Randomization Unit where
  toFun t := if t.val ∈ Set.Icc (0 : ℝ) |r.val| then some () else none
  ωScottContinuous' := by fun_prop
  isHom' := by
    apply Prop.isHom_ite
    · fun_prop
    · fun_prop
    · fun_prop

/-- Sampling lifted to the powerdomain -/
noncomputable def sample_T (_ : Unit) : TX FlatReal :=
  E_T (X := FlatReal) (sample_map ())

/-- Conditioning lifted to the powerdomain -/
noncomputable def score_T (r : FlatReal) : TX Unit :=
  E_T (X := Unit) (score_map r)

end ExpectationMonad
end OmegaQuasiBorelSpace
