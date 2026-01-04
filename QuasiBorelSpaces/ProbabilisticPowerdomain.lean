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
abbrev RX (X : Type*) [OmegaQuasiBorelSpace X] := FlatReal →ω𝒒 Option X

/-- Domain of a randomization -/
def dom (α : RX X) : Set FlatReal := {r | α r ≠ none}

/-- Evaluate the expectation of a weight under a randomization -/
def E_map (α : RX X) (w : X →ω𝒒 ENNReal) : ENNReal :=
  ∫⁻ r, (α r).elim 0 w

@[simp, fun_prop]
lemma isHom_E_map : IsHom (fun x : RX X × _ ↦ E_map x.1 x.2) := by
  unfold E_map
  fun_prop

@[simp, fun_prop]
lemma ωScottContinuous_E_map : ωScottContinuous (fun x : RX X × _ ↦ E_map x.1 x.2) := by
  unfold E_map
  apply Measure.ωScottContinuous_lintegral
  · apply Option.ωScottContinuous_elim
    · fun_prop
    · simp only [bot_eq_zero']
    · fun_prop
  · intro a
    apply measurable_of_isHom
    fun_prop

/-- Bundle the expectation operator arising from a randomization -/
@[simps]
def E_op (α : RX X) : Cont ENNReal X where
  apply := { toFun := E_map α }

@[simp, fun_prop]
lemma isHom_E_op : IsHom (E_op (X := X)) := by
  unfold E_op
  fun_prop

@[simp, fun_prop]
lemma ωScottContinuous_E_op : ωScottContinuous (E_op (X := X)) := by
  unfold E_op
  fun_prop

/-- The expectation morphism `E : RX → JX` -/
@[simps]
def E : RX X →ω𝒒 Cont ENNReal X where
  toFun := E_op

/-- Monad unit on randomizations (Dirac) -/
@[simps]
def return_R (x : X) : RX X where
  toFun := fun r => if r.val ∈ Set.Icc 0 1 then some x else none
  isHom' := by
    apply Prop.isHom_ite
    · apply isHom_comp'
      · simp only [isHom_ofMeasurableSpace, measurable_mem, measurableSet_Icc]
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
def bind_R {Y} [OmegaQuasiBorelSpace Y] (α : RX X) (k : X →ω𝒒 RX Y) : RX Y where
  toFun r := α (RandomSplit.φ r).1 >>= (k · (RandomSplit.φ r).2)
  ωScottContinuous' := by
    simp only [Option.bind_eq_bind]
    fun_prop
  isHom' := by
    simp only [Option.bind_eq_bind]
    fun_prop

end

section ExpectationMonad

variable (X : Type*) [OmegaQuasiBorelSpace X]

/-- Expectation preserves the monad structure on randomizations -/
theorem E_preserves_return (x : X) :
    E (X := X) (return_R (X := X) x) = Cont.unit x := by
  ext w
  change E_map (return_R x) w = w x
  unfold E_map return_R

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

  simp only [h_vol, Set.mem_Icc, OmegaQuasiBorelHom.coe_mk]
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

theorem E_preserves_bind {Y} [OmegaQuasiBorelSpace Y] (α : RX X) (k : X →ω𝒒 RX Y) :
    E (bind_R α k) = Cont.bind (E.comp k) (E α) := by
  ext w
  change E_map (bind_R α k) w = ((E α).bind (E.comp k)).apply w
  unfold Cont.bind
  dsimp only [OmegaQuasiBorelHom.coe_mk, OmegaQuasiBorelHom.comp_coe, E_coe, E_op_apply_coe]
  unfold E_map
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

  have h_lhs : ∫⁻ r, (bind_R α k r).elim 0 w ∂volume = ∫⁻ p, f p ∂(volume.prod volume) := by
    simp only [bind_R]
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
  simp [f]
  cases h : α r1 with
  | none => simp only [Option.bind_none, Option.elim_none, lintegral_const, zero_mul]
  | some x => simp only [Option.bind_some, Option.elim_some]

-- /-
-- ## Randomizable operators and ω-closures (See Section 4.2 of [VakarKS19])
-- -/

/-- Predicate: expectation operator arising from a randomization -/
def Randomizable (μ : Cont ENNReal X) : Prop := ∃ α : RX X, μ = E_op (X := X) α

/-- Randomizable expectation operators as a subtype -/
def SX := {μ : Cont ENNReal X // Randomizable (X := X) μ}
/-- Randomizations valued in randomizations -/
abbrev MRX := FlatReal →ω𝒒 RX X
/-- Randomizable random operators (random elements of `Cont ENNReal`) -/
abbrev MSX := FlatReal →ω𝒒 Cont ENNReal X

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
    · let f : OrderHom FlatReal (Cont ENNReal X) :=
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
inductive InTX : Cont ENNReal X → Prop
  /-- Randomizable operators are in the closure -/
  | randomizable (α : RX X) : InTX (E_op (X := X) α)
  /-- The closure is closed under ω-sups -/
  | sup {c : Chain (Cont ENNReal X)} : (∀ n, InTX (c n)) → InTX (ωSup c)

/-- Membership in the ω-sup-closure of randomizable random operators -/
inductive InMTX : MSX X → Prop
  /-- Randomizable random operators are in the closure -/
  | randomizable (β : MRX X) : InMTX (E_rand (X := X) β)
  /-- The closure is closed under ω-sups -/
  | sup {c : Chain (MSX X)} : (∀ n, InMTX (c n)) → InMTX (ωSup c)

/-- Probabilistic powerdomain: smallest ω-subcpo of `Cont ENNReal` -/
abbrev TX := {μ : Cont ENNReal X // InTX (X := X) μ}

/-- Random elements of the powerdomain -/
abbrev MTX := {β : MSX X // InMTX (X := X) β}

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
noncomputable def E_T (α : RX X) : TX X :=
  ⟨E_op (X := X) α, InTX.randomizable α⟩

/-- Pointwise extension of `E_T` to random randomizations -/
noncomputable def E_MT (β : MRX X) : MTX X :=
  ⟨E_rand (X := X) β, InMTX.randomizable β⟩

/-- `TX` inherits an ωCPO structure from `Cont ENNReal` -/
noncomputable instance : OmegaCompletePartialOrder (TX X) where
  ωSup := fun c =>
    let incl : OrderHom (TX X) (Cont ENNReal X) :=
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
        exact hx n))

/-- `TX` is an ωQBS as a full subobject of `Cont ENNReal` -/
noncomputable instance : OmegaQuasiBorelSpace (TX X) where
  isHom_ωSup' := by
    intro c hc
    rw [QuasiBorelSpace.Subtype.isHom_def]
    let c' : Chain (ℝ → Cont ENNReal X) := {
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
    exact hcn

/-- `MTX` inherits an ωCPO structure from `MSX` -/
noncomputable instance : OmegaCompletePartialOrder (MTX X) where
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
        exact hx n))

/-- `MTX` is an ωQBS as a full subobject of `MSX` -/
noncomputable instance : OmegaQuasiBorelSpace (MTX X) where
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
    exact hcn

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
    ωScottContinuous' :=
      -- TODO: we should be able to infer this automatically if we make TX a
      -- structure with appropriate lemmas
      sorry
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
