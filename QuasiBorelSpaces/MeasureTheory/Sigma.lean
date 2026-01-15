module

public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import QuasiBorelSpaces.MeasureTheory.Cases

public section

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

lemma measurable_cast
    (ix : A → I) (i : I)
    (p : ∀ x, ix x = i)
    (f : ∀ x, P (ix x)) (hf : Measurable fun x ↦ (⟨ix x, f x⟩ : Sigma P))
    : Measurable fun x : A ↦ cast (congr_arg P (p x)) (f x) := by
  intro X hX
  have : (fun x ↦ cast (congr_arg P (p x)) (f x)) ⁻¹' X
       = {x | Sigma.mk (ix x) (f x) ∈ Sigma.mk i '' X} := by
    grind
  rw [this]
  apply hf
  simp only [
    MeasurableSpace.measurableSet_sInf, Set.mem_range,
    forall_exists_index, forall_apply_eq_imp_iff]
  intro j
  rw [MeasurableSpace.map_def]
  by_cases h : i = j
  · subst h
    simp only [
      Set.preimage, Set.mem_image, Sigma.mk.injEq, heq_eq_eq,
      true_and, exists_eq_right, Set.setOf_mem_eq, hX]
  · simp only [
      Set.preimage, Set.mem_image, Sigma.mk.injEq, h, false_and,
      and_false, exists_false, Set.setOf_false, MeasurableSet.empty]

lemma measurable_eq_rec
    (ix : A → I) (i : I)
    (p : ∀ x, ix x = i)
    (f : ∀ x, P (ix x)) (hf : Measurable fun x ↦ (⟨ix x, f x⟩ : Sigma P))
    : Measurable fun x : A ↦ p x ▸ f x := by
  simp only [eqRec_eq_cast]
  apply measurable_cast
  · exact p
  · exact hf

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
      · apply measurable_eq_rec
        simp only [Sigma.eta]
        apply Measurable.comp'
        · fun_prop
        · apply Measurable.subtype_val
          fun_prop
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

instance [∀ i, DiscreteMeasurableSpace (P i)] : DiscreteMeasurableSpace (Sigma P) where
  forall_measurableSet X := by
    simp only [
      MeasurableSpace.measurableSet_sInf, Set.mem_range,
      forall_exists_index, forall_apply_eq_imp_iff]
    intro i
    rw [MeasurableSpace.map_def]
    apply MeasurableSet.of_discrete

end MeasureTheory.Sigma
