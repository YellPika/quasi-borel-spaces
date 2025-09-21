import QuasiBorelSpaces.Hom
import QuasiBorelSpaces.List.Encoding
import QuasiBorelSpaces.MeasureTheory.List
import QuasiBorelSpaces.Pi
import QuasiBorelSpaces.ProbabilityMeasure
import QuasiBorelSpaces.Sigma

variable {A B C : Type*} [QuasiBorelSpace A] [QuasiBorelSpace B] [QuasiBorelSpace C]

namespace List.Encoding

open QuasiBorelSpace

@[fun_prop]
lemma isHom_cons : IsHom (fun x : A × List.Encoding A ↦ cons x.1 x.2) := by
  apply Sigma.isHom_distrib'
  apply Sigma.isHom_elim
  intro i
  dsimp only [cons]
  apply Sigma.isHom_inj'
  simp only [Pi.isHom_iff]
  intro j
  cases j using Fin.cases with
  | zero => simp only [Fin.cases_zero, Prod.isHom_fst]
  | succ i =>
    simp only [Fin.cases_succ]
    fun_prop

@[fun_prop]
lemma isHom_fold
      {cons : A → B → B} (hcons : IsHom fun (x, y) ↦ cons x y) (nil : B)
    : IsHom (foldr cons nil) := by
  apply Sigma.isHom_elim
  intro i
  induction i with
  | zero => simp only [foldr, isHom_const]
  | succ n ih =>
    simp only [foldr]
    apply Prod.isHom_of_uncurry
    · exact hcons
    · fun_prop
    · apply isHom_comp' ih
      fun_prop

end List.Encoding

namespace QuasiBorelSpace.List

instance : QuasiBorelSpace (List A) := lift List.encode

@[simp, fun_prop]
lemma isHom_encode : IsHom (List.encode (A := A)) := by
  apply isHom_of_lift

@[simp, fun_prop]
lemma isHom_cons : IsHom (fun x : A × List A ↦ x.1 :: x.2) := by
  simp only [isHom_to_lift, List.encode_cons]
  fun_prop

lemma isHom_cons'
    {f : A → B} (hf : IsHom f)
    {g : A → List B} (hg : IsHom g)
    : IsHom (fun x ↦ f x :: g x) := by
  fun_prop

@[local fun_prop]
lemma isHom_foldr
    {cons : A → B → B} (hcons : IsHom fun (x, xs) ↦ cons x xs) (nil : B)
    : IsHom (List.foldr cons nil) := by
  have : List.foldr cons nil = fun xs ↦ List.Encoding.foldr cons nil (List.encode xs) := by
    ext xs
    induction xs with
    | nil =>
      simp only [List.foldr_nil, List.encode_nil, List.Encoding.foldr_nil]
    | cons head tail ih =>
      simp only [List.foldr_cons, ih, List.encode_cons, List.Encoding.foldr_cons]
  rw [this]
  fun_prop

@[fun_prop]
lemma isHom_foldr'
    {cons : A → B → C → C} (hcons : IsHom fun (x, y, z) ↦ cons x y z)
    {nil : A → C} (hnil : IsHom nil)
    {f : A → List B} (hf : IsHom f)
    : IsHom (fun x ↦ List.foldr (cons x) (nil x) (f x)) := by
  have {x}
      : List.foldr (cons x) (nil x) (f x)
      = List.foldr (β := A →𝒒 C) (fun x k ↦ .mk (fun y ↦ cons y x (k y))) (.mk nil) (f x) x := by
    induction f x with
    | nil => simp only [List.foldr_nil, QuasiBorelHom.coe_mk]
    | cons x xs ih => simp only [List.foldr_cons, ih, QuasiBorelHom.coe_mk]
  simp only [this]
  fun_prop

@[fun_prop]
lemma isHom_map
    {f : A → B → C} (hf : IsHom fun (x, y) ↦ f x y)
    {g : A → List B} (hg : IsHom g)
    : IsHom (fun x ↦ List.map (f x) (g x)) := by
  have {f : B → C} {xs : List B} : List.map f xs = List.foldr (fun x ↦ (f x :: ·)) [] xs := by
    simp only [List.foldr_cons_eq_append, List.append_nil]
  simp only [this]
  fun_prop

instance
    [MeasurableSpace A] [MeasurableQuasiBorelSpace A]
    : MeasurableQuasiBorelSpace (List A) where
  isVar_iff_measurable φ := by
    simp [MeasureTheory.List.measurable_to_encode, ← isHom_iff_isVar, isHom_to_lift]
    simp only [isHom_iff_isVar]
    rw [isVar_iff_measurable]

@[simp]
noncomputable def sequence : List (ProbabilityMeasure A) → ProbabilityMeasure (List A)
  | [] => .unit []
  | μ :: μs => .bind (fun x ↦ .map (x :: ·) (sequence μs)) μ

@[simp]
noncomputable def lintegral (k : List A → ENNReal) : List (ProbabilityMeasure A) → ENNReal
  | [] => k []
  | μ :: μs => μ.lintegral fun x ↦ lintegral (fun xs ↦ k (x :: xs)) μs

@[simp]
lemma lintegral_sequence
    (μs : List (ProbabilityMeasure A))
    (k : List A → ENNReal) (hk : IsHom k)
    : (sequence μs).lintegral k = lintegral k μs := by
  induction μs generalizing k with
  | nil => simp (disch := fun_prop) only [sequence, ProbabilityMeasure.lintegral_unit, lintegral]
  | cons head tail ih =>
    have : IsHom (fun x ↦ ProbabilityMeasure.map (x :: ·) (sequence tail)) := by fun_prop
    simp (disch := fun_prop) only [
      sequence, ProbabilityMeasure.lintegral_bind,
      ProbabilityMeasure.lintegral_map, ih, lintegral]

end QuasiBorelSpace.List
