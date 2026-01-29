module

import Mathlib.Probability.Kernel.MeasurableLIntegral
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.GiryMonad
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.Probability.Kernel.Defs

public section

namespace MeasureTheory.Measure

variable {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]

lemma measurable_map'
    {f : A → B → C} (hf : Measurable fun (x, y) ↦ f x y)
    {μ : A → Measure B} (hμ₁ : Measurable μ) [∀ x, IsFiniteMeasure (μ x)]
    : Measurable (fun x ↦ map (f x) (μ x)) := by
  apply measurable_of_measurable_coe
  intro X hX
  have hf' (x) : Measurable (f x) := by
    apply Measurable.of_uncurry_left
    exact hf
  simp only [hf', hX, map_apply]
  let κ : ProbabilityTheory.Kernel A B := ⟨μ, hμ₁⟩

  change Measurable fun b ↦ κ b (Prod.mk b ⁻¹' (Function.uncurry f ⁻¹' X))
  apply ProbabilityTheory.Kernel.measurable_kernel_prodMk_left_of_finite
  · apply hf hX
  · infer_instance

lemma measurable_apply
    {μ : A → Measure B} (hμ : Measurable μ) (hμ' : ProbabilityTheory.IsSFiniteKernel ⟨μ, hμ⟩)
    {i : A → Set B} (hi : Measurable fun x : _ × _ ↦ x.1 ∈ i x.2)
    : Measurable (fun x ↦ μ x (i x)) := by
  have hi' {x} : MeasurableSet (i x) := by
    change MeasurableSet { a | a ∈ i x }
    rw [measurableSet_setOf]
    have : Measurable (fun y : B ↦ (y, x)) := by fun_prop
    apply Measurable.comp' hi this
  simp only [← MeasureTheory.lintegral_indicator_one, hi']
  apply Measurable.lintegral_kernel_prod_left (κ := ⟨μ, hμ⟩)
  apply Measurable.ite
  · simp only [measurableSet_setOf]
    fun_prop
  · fun_prop
  · fun_prop

end MeasureTheory.Measure
