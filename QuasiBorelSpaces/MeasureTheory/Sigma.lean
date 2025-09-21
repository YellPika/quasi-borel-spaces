import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.Tactic.FunProp
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import QuasiBorelSpaces.MeasureTheory.Cases

namespace MeasureTheory.Sigma

universe u

variable
  {I : Type*} {P : I → Type*} [∀ i, MeasurableSpace (P i)]
  {A : Type*} [MeasurableSpace A]
  {B : Type u} [MeasurableSpace B]
  {C : Type u} [MeasurableSpace C]

@[fun_prop]
lemma measurable_mk (i : I) : Measurable (⟨i, ·⟩ : P i → Sigma P) := by
  intro X hX
  simp only [
    MeasurableSpace.measurableSet_sInf, Set.mem_range,
    forall_exists_index, forall_apply_eq_imp_iff] at hX
  apply hX

lemma measurable_mk'
    (i : I) {f : A → P i} (hf : Measurable f)
    : Measurable (fun x ↦ (⟨i, f x⟩ : Sigma P)) := by
  fun_prop

lemma measurable_elim
    {f : Sigma P → A} (hf : ∀ i, Measurable (fun x ↦ f ⟨i, x⟩))
    : Measurable f := by
  intro X hX
  simp only [
    MeasurableSpace.measurableSet_sInf, Set.mem_range,
    forall_exists_index, forall_apply_eq_imp_iff]
  intro i
  rw [MeasurableSpace.map_def]
  simp only [Set.preimage, Set.mem_setOf_eq]
  apply hf
  exact hX

lemma measurable_elim'
    {f : ∀ i, P i → A} (hf : ∀ i, Measurable (f i))
    {g : A → (i : I) × P i} (hg : Measurable g)
    : Measurable (fun x ↦ f (g x).1 (g x).2) := by
  apply Measurable.comp' (g := fun x : Sigma P ↦ (f x.1 x.2 : A)) (f := g)
  · exact measurable_elim hf
  · exact hg

@[fun_prop, simp]
lemma measurable_fst [MeasurableSpace I] : Measurable (Sigma.fst : Sigma P → I) := by
  intro X hX
  simp only [
    MeasurableSpace.measurableSet_sInf, Set.mem_range,
    forall_exists_index, forall_apply_eq_imp_iff]
  intro i
  rw [MeasurableSpace.map_def]
  simp only [Set.preimage, Set.mem_setOf_eq, measurableSet_setOf, measurable_const]

lemma measurable_distrib [Countable I]
    : Measurable (fun x : A × Sigma P ↦ (⟨x.2.1, x.1, x.2.2⟩ : (i : I) × A × P i)) := by
  classical

  wlog h : Nonempty ((i : I) × A × P i)
  · simp only [not_nonempty_iff] at h
    apply measurable_of_empty_codomain

  let ix (x : A × Sigma P) := x.2.1
  have hix : Measurable[_, ⊤] ix := by
    simp only [ix]
    fun_prop

  let f (i : I) (x : A × Sigma P) : (i : I) × A × P i :=
    if h : x.2.1 = i then ⟨i, x.1, h ▸ x.2.2⟩ else Classical.arbitrary _
  have hf (i) : Measurable (f i) := by
    apply measurable_dite
    · apply measurable_cases (ix := fun x : A × Sigma P ↦ x.2.fst) (f := fun j _ ↦ j = i)
      · fun_prop
      · fun_prop
    · apply measurable_mk'
      apply Measurable.prodMk
      · apply Measurable.comp'
        · fun_prop
        · apply Measurable.subtype_val
          fun_prop
      · intro X hX
        simp [Subtype.instMeasurableSpace, MeasurableSpace.measurableSet_comap]
        use {x | ∃(h : x.2.1 = i), h ▸ x.2.2 ∈ X }
        apply And.intro
        · constructor
          simp only [Set.sup_eq_union, Set.mem_union, Set.mem_setOf_eq]
          right
          simp only [
            MeasurableSpace.measurableSet_comap, MeasurableSpace.measurableSet_sInf,
            Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff]
          use {x | ∃ (h : x.fst = i), h ▸ x.snd ∈ X}
          simp only [Set.preimage_setOf_eq, and_true]
          intro j
          simp only [MeasurableSpace.map_def, Set.preimage_setOf_eq]
          simp only [Set.preimage_setOf_eq]
          by_cases h : j = i
          · subst h
            simp only [exists_const, Set.setOf_mem_eq]
            exact hX
          · simp only [h, IsEmpty.exists_iff, Set.setOf_false, MeasurableSet.empty]
        · ext
          simp only [Set.preimage_setOf_eq, Set.mem_setOf_eq, Set.mem_preimage]
          apply Iff.intro
          · rintro ⟨h, x⟩
            exact x
          · intro h
            exact ⟨_, h⟩
    · fun_prop

  have : (fun x ↦ ⟨x.2.fst, (x.1, x.2.snd)⟩) = (fun x ↦ f (ix x) x) := by
    ext x : 1
    simp only [↓reduceDIte, f, ix]
  rw [this]
  apply measurable_cases
  · fun_prop
  · fun_prop

lemma measurable_distrib' [Countable I]
    {f : A × Sigma P → B} (hf : Measurable (fun x : (i : I) × A × P i ↦ f ⟨x.2.1, x.1, x.2.2⟩))
    : Measurable f := by
  apply Measurable.comp'
      (g := fun x : (i : I) × A × P i ↦ f ⟨x.2.1, x.1, x.2.2⟩)
      (f := fun x : A × Sigma P ↦ ⟨x.2.1, x.1, x.2.2⟩)
  · exact hf
  · apply measurable_distrib

end MeasureTheory.Sigma
