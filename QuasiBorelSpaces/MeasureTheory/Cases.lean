import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Instances

open scoped MeasureTheory

namespace MeasureTheory

variable
  {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
  {I : Type*} [Countable I]

lemma measurable_cases
    {ix : A → I} {f : I → A → B}
    (hix : Measurable[_, ⊤] ix) (hf : ∀ i, Measurable (f i))
    : Measurable (fun x ↦ f (ix x) x) := by
  intro s hs

  have : ((fun x ↦ f (ix x) x) ⁻¹' s) = ⋃i, { x | ix x ∈ ({i} : Set I) } ∩ { x | f i x ∈ s } := by
    ext
    simp only [
      Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iUnion,
      Set.mem_inter_iff, Set.mem_setOf_eq, exists_eq_left']
  rw [this]

  refine MeasurableSet.iUnion fun i ↦ MeasurableSet.inter ?_ ?_
  · exact hix MeasurableSpace.measurableSet_top
  · exact hf i hs


@[fun_prop]
lemma measurable_decide
    {p : A → Prop} [inst : DecidablePred p] (hp : Measurable p)
    : Measurable (fun x ↦ decide (p x)) := by
  classical
  have : inst = fun x ↦ Classical.dec (p x) := by subsingleton
  subst this
  apply measurable_cases (f := fun p _ ↦ decide p)
  · exact hp
  · simp only [measurable_const, implies_true]

end MeasureTheory
