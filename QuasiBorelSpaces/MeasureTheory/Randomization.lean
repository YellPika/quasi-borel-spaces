module

import Mathlib.Analysis.SpecialFunctions.Sigmoid
import QuasiBorelSpaces.MeasureTheory.Pack
import QuasiBorelSpaces.MeasureTheory.Quantile
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.MeasureTheory.Constructions.UnitInterval
public import Mathlib.MeasureTheory.Measure.GiryMonad
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

public section

open scoped unitInterval

namespace MeasureTheory.Measure

variable {A B} [MeasurableSpace A] [MeasurableSpace B]

/-- The function `det μ` is a function such that `volume.map (det μ) = μ`. -/
noncomputable def det [StandardBorelSpace A] (μ : Measure A) [IsProbabilityMeasure μ] : I → A :=
  have : IsProbabilityMeasure (μ.map (unpack (A := I) ∘ pack)) := by
    apply Measure.isProbabilityMeasure_map
    fun_prop
  have := MeasureTheory.nonempty_of_isProbabilityMeasure μ
  unpack ∘ pack ∘ quantile (μ.map (unpack (A := I) ∘ pack))

@[fun_prop]
lemma measurable_det
    [StandardBorelSpace B]
    {μ : A → Measure B} [∀ x, IsProbabilityMeasure (μ x)] (hμ : Measurable μ)
    {i : A → I} (hi : Measurable i)
    : Measurable fun x ↦ det (μ x) (i x) := by
  simp only [det, Function.comp_apply]
  wlog hA : Nonempty A
  · simp only [not_nonempty_iff] at hA
    apply measurable_of_empty
  have hB : Nonempty B := MeasureTheory.nonempty_of_isProbabilityMeasure (μ hA.some)
  have {x} : IsProbabilityMeasure (Measure.map (unpack (A := I) ∘ pack) (μ x)) := by
    apply Measure.isProbabilityMeasure_map
    fun_prop
  apply Measurable.comp (measurable_unpack (A := B))
  fun_prop

@[simp]
private lemma unitInterval.not_countable : ¬Countable I := by
  intro h
  have := Function.Injective.countable unitInterval.sigmoid_injective
  simp only [_root_.not_countable] at this

@[simp]
lemma eq_det_volume
    [StandardBorelSpace A] (μ : Measure A) [IsProbabilityMeasure μ]
    : volume.map (det μ) = μ := by
  have : IsProbabilityMeasure (Measure.map (unpack (A := I) ∘ pack) μ) := by
    apply Measure.isProbabilityMeasure_map
    fun_prop
  rw [det, ← Measure.map_map, ← Measure.map_map]
  · simp only [eq_quantile_volume]
    rw [Measure.map_map, Measure.map_map]
    · simp +unfoldPartialApp only [
        Function.comp, unitInterval.not_countable,
        not_false_eq_true, pack_unpack, unpack_pack, map_id']
    · fun_prop
    · fun_prop
    · fun_prop
    · fun_prop
  · fun_prop
  · apply measurable_quantile <;> fun_prop
  · fun_prop
  · apply Measurable.comp measurable_pack
    apply measurable_quantile <;> fun_prop

end MeasureTheory.Measure
