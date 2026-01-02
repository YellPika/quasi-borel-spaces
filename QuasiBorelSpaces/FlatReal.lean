import QuasiBorelSpaces.OmegaQuasiBorelSpace
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
  isHom_ωSup' _ hc := hc 0

end FlatReal
