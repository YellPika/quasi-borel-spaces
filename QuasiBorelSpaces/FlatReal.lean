import QuasiBorelSpaces.OmegaQuasiBorelSpace
import QuasiBorelSpaces.OmegaCompletePartialOrder.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite

open MeasureTheory
open MeasureSpace

/-- Reals with the Lebesgue measure and a discrete ωCPO structure. -/
structure FlatReal where
  /-- The underlying real number. -/
  val : ℝ

namespace FlatReal

instance : Inhabited FlatReal := ⟨⟨0⟩⟩

instance : MeasurableSpace FlatReal :=
  MeasurableSpace.comap FlatReal.val (inferInstance : MeasurableSpace ℝ)

noncomputable instance : MeasureSpace FlatReal where
  volume := Measure.map FlatReal.mk volume

@[simp, fun_prop]
lemma R.measurable_mk : Measurable FlatReal.mk := by
  rw [measurable_comap_iff]
  apply measurable_id

@[simp, fun_prop]
lemma R.measurable_val : Measurable FlatReal.val := by
  apply comap_measurable

noncomputable instance : SigmaFinite (volume : Measure FlatReal) :=
  MeasurableEquiv.sigmaFinite_map {
    toFun := FlatReal.mk
    invFun := FlatReal.val
    left_inv _ := rfl
    right_inv _ := rfl
    measurable_toFun := by simp only [Equiv.coe_fn_mk, R.measurable_mk]
    measurable_invFun := by simp only [Equiv.coe_fn_symm_mk, R.measurable_val]
  }

instance : QuasiBorelSpace FlatReal := QuasiBorelSpace.ofMeasurableSpace

instance : PartialOrder FlatReal where
  le x y := x = y
  le_refl _ := rfl
  le_trans _ _ _ h₁ h₂ := h₁.trans h₂
  le_antisymm _ _ h₁ _ := h₁

/-- `FlatReal` is trivially an ωCPO: chains are constant by discreteness. -/
instance : OmegaCompletePartialOrder FlatReal where
  ωSup c := c 0
  le_ωSup c n := by rw [c.monotone (Nat.zero_le n)]
  ωSup_le c x hx := by rw [hx 0]

/-- `FlatReal` is trivially an ωQBS. -/
instance : OmegaQuasiBorelSpace FlatReal where
  isHom_ωSup := by
    change QuasiBorelSpace.IsHom fun c : OmegaCompletePartialOrder.Chain FlatReal ↦ c 0
    fun_prop

instance : TopologicalSpace FlatReal :=
  TopologicalSpace.induced val inferInstance

instance : BorelSpace FlatReal where
  measurable_eq := by
    simp only [instMeasurableSpace, inferInstance, Real.measurableSpace, ← borel_comap]

instance : PolishSpace FlatReal :=
  Equiv.polishSpace_induced (α := FlatReal) (β := ℝ) {
    toFun := val
    invFun := mk
    left_inv _ := rfl
    right_inv _ := rfl
  }

instance : StandardBorelSpace FlatReal where
  polish := ⟨inferInstance, inferInstance, inferInstance⟩

@[simp]
lemma le_iff_eq {x y : FlatReal} : x ≤ y ↔ x = y := by rfl

open OmegaCompletePartialOrder

@[simp, fun_prop]
lemma ωScottContinuous_of
    {A : Type*} [OmegaCompletePartialOrder A] (f : FlatReal → A)
    : ωScottContinuous f := by
  rw [ωScottContinuous_iff_monotone_map_ωSup]
  refine ⟨fun x y hxy ↦ ?_, fun c ↦ ?_⟩
  · simp only [le_iff_eq] at hxy
    simp only [hxy, le_refl]
  · simp only [ωSup]
    apply le_antisymm
    · apply le_ωSup_of_le 0
      simp only [Chain.map_coe, OrderHom.coe_mk, Function.comp_apply, le_refl]
    · simp only [ωSup_le_iff, Chain.map_coe, OrderHom.coe_mk, Function.comp_apply]
      intro i
      apply le_of_eq
      congr 1
      symm
      apply c.monotone
      simp only [zero_le]

end FlatReal
