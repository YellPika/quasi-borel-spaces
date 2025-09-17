import Mathlib.Probability.Kernel.MeasurableLIntegral

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

end MeasureTheory.Measure
