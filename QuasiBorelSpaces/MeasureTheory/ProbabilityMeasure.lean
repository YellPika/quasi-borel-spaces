import Mathlib.Probability.Kernel.MeasurableLIntegral
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

namespace MeasureTheory

variable {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]

lemma isProbabilityMeasure_bind
    {f : A → Measure B} [∀ x, IsProbabilityMeasure (f x)] (hf : Measurable f)
    (μ : Measure A) [IsProbabilityMeasure μ]
    : IsProbabilityMeasure (μ.bind f) := by
  let κ : ProbabilityTheory.Kernel A B := ⟨f, hf⟩
  have : ProbabilityTheory.IsMarkovKernel κ := ⟨fun _ ↦ inferInstance⟩
  have : MeasureTheory.IsProbabilityMeasure (μ.bind κ) := inferInstance
  exact this

/-- Monadic bind for probability measures. -/
noncomputable def ProbabilityMeasure.bind
    (μ : ProbabilityMeasure A)
    (f : A → ProbabilityMeasure B)
    : ProbabilityMeasure B :=
  open Classical in
  if h : Measurable f then
    {
      val := μ.toMeasure.bind fun x ↦ (f x).toMeasure,
      property := by
        apply isProbabilityMeasure_bind
        apply Measurable.subtype_val
        exact h
    }
  else
    f μ.nonempty.some

lemma ProbabilityMeasure.lintegral_bind
    (μ : ProbabilityMeasure A)
    {f : A → ProbabilityMeasure B} (hf : Measurable f)
    {k : B → ENNReal} (hk : Measurable k)
    : ∫⁻ x, k x ∂μ.bind f = ∫⁻ a, ∫⁻ x, k x ∂f a ∂μ := by
  simp only [bind, hf, ↓reduceDIte, coe_mk]
  rw [MeasureTheory.Measure.lintegral_bind]
  · apply hf.subtype_val.aemeasurable
  · apply hk.aemeasurable

@[fun_prop]
lemma ProbabilityMeasure.measurable_bind
    (f : A → ProbabilityMeasure B)
    : Measurable (bind · f) := by
  wlog hA : Nonempty (ProbabilityMeasure A)
  · simp only [not_nonempty_iff] at hA
    apply measurable_of_empty

  wlog hf : Measurable f
  · simp only [bind, hf, ↓reduceDIte]
    change Measurable fun _ ↦ f hA.some.nonempty.some
    apply measurable_const

  simp only [bind, hf, ↓reduceDIte]
  apply Measurable.subtype_mk
  apply Measurable.comp' (MeasureTheory.Measure.measurable_bind' ?_)
  · apply Measurable.subtype_val
    apply measurable_id'
  · apply hf.subtype_val

end MeasureTheory
