import QuasiBorelSpaces.ProbabilityMeasure
import QuasiBorelSpaces.Hom
import QuasiBorelSpaces.Pi
import QuasiBorelSpaces.Sigma

namespace QuasiBorelSpace.List

variable {A B C : Type*} [QuasiBorelSpace A] [QuasiBorelSpace B] [QuasiBorelSpace C]

/--
We derive the `QuasiBorelSpace` instance for `List A`s from their encoding as
`(n : ℕ) × (Fin n → A)`.
-/
abbrev Encoding (A : Type*) :=
  (n : ℕ) × (Fin n → A)

namespace Encoding

/-- The encoded version of `[]`. -/
def nil : Encoding A := ⟨0, Fin.elim0⟩

/-- The encoded version of `· ∷ ·`. -/
def cons (x : A) (xs : Encoding A) : Encoding A :=
  ⟨xs.1 + 1, Fin.cases x xs.2⟩

/-- The encoded version of `List.foldr`. -/
def foldr (cons : A → B → B) (nil : B) : Encoding A → B
  | ⟨0, _⟩ => nil
  | ⟨n + 1, k⟩ => cons (k 0) (foldr cons nil ⟨n, fun i ↦ k i.succ⟩)

@[simp]
lemma foldr_nil {A B} (f : A → B → B) (z : B) : foldr f z nil = z := by
  simp only [nil, foldr]

@[simp]
lemma foldr_cons {A B}
    (f : A → B → B) (z : B) (x : A) (xs : Encoding A)
    : foldr f z (cons x xs) = f x (foldr f z xs) := by
  simp only [cons, foldr, Fin.cases_zero, Fin.cases_succ, Sigma.eta]

@[fun_prop]
lemma isHom_cons : IsHom (fun x : A × Encoding A ↦ cons x.1 x.2) := by
  unfold cons
  apply Sigma.isHom_distrib'
  apply Sigma.isHom_elim
  intro i
  dsimp only
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
    : IsHom (Encoding.foldr cons nil) := by
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

end Encoding

/-- Encodes a `List A` as an `Encoding A`. -/
def encode : List A → Encoding A :=
  List.foldr Encoding.cons Encoding.nil

@[simp]
lemma encode_nil {A} : encode (A := A) [] = Encoding.nil := rfl

@[simp]
lemma encode_cons {A} (x : A) (xs : List A) : encode (x :: xs) = Encoding.cons x (encode xs) := rfl

instance : QuasiBorelSpace (List A) := lift encode

@[simp, fun_prop]
lemma isHom_encode : IsHom (encode (A := A)) := by
  apply isHom_of_lift

@[simp, fun_prop]
lemma isHom_cons : IsHom (fun x : A × List A ↦ x.1 :: x.2) := by
  simp only [isHom_to_lift]
  have (x : A) (xs : List A) : encode (x :: xs) = Encoding.cons x (encode xs) := rfl
  simp only [this]
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
  have : List.foldr cons nil = fun xs ↦ Encoding.foldr cons nil (encode xs) := by
    ext xs
    induction xs with
    | nil => simp only [List.foldr_nil, encode_nil, Encoding.foldr_nil]
    | cons head tail ih => simp only [List.foldr_cons, encode_cons, Encoding.foldr_cons, ih]
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
