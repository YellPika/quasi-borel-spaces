module

public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.Tactic.FunProp
public import QuasiBorelSpaces.List.Encoding
import QuasiBorelSpaces.MeasureTheory.Sigma

public section

variable
  {A : Type*} [MeasurableSpace A]
  {B : Type*} [MeasurableSpace B]
  {C : Type*} [MeasurableSpace C]

namespace List.Encoding

open MeasureTheory

@[fun_prop, simp]
lemma measurable_cons : Measurable (fun x : A × Encoding A ↦ cons x.1 x.2) := by
  apply Sigma.measurable_distrib'
  apply Sigma.measurable_elim
  intro n
  simp only [cons]
  apply Sigma.measurable_mk'
  apply measurable_pi_lambda
  rintro ⟨i, _⟩
  cases i with
  | zero =>
    simp only [Fin.zero_eta, Fin.cases_zero]
    fun_prop
  | succ n =>
    simp only [Fin.cases_succ']
    fun_prop

@[fun_prop]
lemma measurable_fold
      {cons : A → B → B} (hcons : Measurable fun (x, y) ↦ cons x y) (nil : B)
    : Measurable (Encoding.foldr cons nil) := by
  apply Sigma.measurable_elim
  intro i
  induction i with
  | zero =>
    have {x : Fin 0 → A} : ⟨0, x⟩ = Encoding.nil := by
      simp only [Encoding.nil, Sigma.mk.injEq, heq_eq_eq, true_and]
      ext i
      apply Fin.elim0 i
    simp only [this, foldr_nil, measurable_const]
  | succ n ih =>
    have {x : Fin (n + 1) → A} : ⟨n + 1, x⟩ = Encoding.cons (x 0) ⟨n, x ∘ Fin.succ⟩ := by
      simp only [Encoding.cons, Sigma.mk.injEq, heq_eq_eq, true_and]
      ext i
      cases i using Fin.cases <;> rfl
    simp only [this, foldr_cons]
    apply Measurable.comp'
      (g := fun x : _ × _ ↦ cons x.1 x.2)
      (f := fun x ↦ (_, _))
    · assumption
    · apply Measurable.prodMk
      · fun_prop
      · apply Measurable.comp' ih
        fun_prop

end List.Encoding

namespace MeasureTheory.List

instance : MeasurableSpace (List A) :=
  MeasurableSpace.comap List.Encoding.encode inferInstance

@[fun_prop]
lemma measurable_encode : Measurable (List.Encoding.encode (A := A)) := by
  apply comap_measurable

@[local simp]
lemma measurable_to_encode
    (f : A → List B)
    : Measurable f ↔ Measurable (fun x ↦ List.Encoding.encode (f x)) := by
  rw [measurable_iff_comap_le]
  apply Iff.intro
  · intro h X hX
    apply h
    simp only [
      MeasurableSpace.measurableSet_comap, MeasurableSpace.measurableSet_sInf,
      Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff,
      exists_exists_and_eq_and]
    use X
    simp only [Set.preimage, Set.mem_setOf_eq, and_true]
    simp only [
      MeasurableSpace.measurableSet_sInf, Set.mem_range,
      forall_exists_index, forall_apply_eq_imp_iff] at hX
    exact hX
  · intro h X hX
    simp only [
      MeasurableSpace.measurableSet_comap, MeasurableSpace.measurableSet_sInf,
      Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff,
      exists_exists_and_eq_and] at hX
    rcases hX with ⟨Y, hY, rfl⟩
    apply h
    simp only [
      MeasurableSpace.measurableSet_sInf, Set.mem_range,
      forall_exists_index, forall_apply_eq_imp_iff]
    exact hY

@[local fun_prop, simp]
lemma measurable_cons : Measurable (fun ((x : A), xs) ↦ x :: xs) := by
  simp only [measurable_to_encode, List.Encoding.encode_cons]
  fun_prop

@[fun_prop]
lemma measurable_cons'
    {f : A → B} (hf : Measurable f)
    {g : A → List B} (hg : Measurable g)
    : Measurable (fun x ↦ f x :: g x) := by
  fun_prop

@[fun_prop]
lemma measurable_foldr
    {cons : A → B → B} (hcons : Measurable fun (x, xs) ↦ cons x xs) (nil : B)
    : Measurable (List.foldr cons nil) := by
  have : List.foldr cons nil = fun xs ↦ List.Encoding.foldr cons nil (.encode xs) := by
    ext xs
    induction xs with
    | nil =>
      simp only [List.foldr_nil, List.Encoding.encode_nil, List.Encoding.foldr_nil]
    | cons head tail ih =>
      simp only [List.foldr_cons, ih, List.Encoding.encode_cons, List.Encoding.foldr_cons]
  rw [this]
  fun_prop

instance [DiscreteMeasurableSpace A] [Countable A] : DiscreteMeasurableSpace (List A) where
  forall_measurableSet X := by
    rw [MeasurableSpace.measurableSet_comap]
    use .encode '' X
    apply And.intro
    · have {n} : DiscreteMeasurableSpace (Fin n → A) := by
        apply MeasurableSingletonClass.toDiscreteMeasurableSpace
      apply MeasurableSet.of_discrete (α := (n : ℕ) × (Fin n → A))
    · rw [Set.preimage_image_eq]
      simp only [List.Encoding.encode_injective]

end MeasureTheory.List
