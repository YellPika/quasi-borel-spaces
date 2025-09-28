import QuasiBorelSpaces.Hom
import QuasiBorelSpaces.List.Encoding
import QuasiBorelSpaces.MeasureTheory.List
import QuasiBorelSpaces.Option
import QuasiBorelSpaces.Nat
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
  apply Sigma.isHom_mk'
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

instance : QuasiBorelSpace (List A) := lift List.Encoding.encode

@[simp, fun_prop]
lemma isHom_encode : IsHom (List.Encoding.encode (A := A)) := by
  apply isHom_of_lift

@[simp, fun_prop]
lemma isHom_cons : IsHom (fun x : A × List A ↦ x.1 :: x.2) := by
  simp only [isHom_to_lift, List.Encoding.encode_cons]
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
  have : List.foldr cons nil = fun xs ↦ List.Encoding.foldr cons nil (List.Encoding.encode xs) := by
    ext xs
    induction xs with
    | nil =>
      simp only [List.foldr_nil, List.Encoding.encode_nil, List.Encoding.foldr_nil]
    | cons head tail ih =>
      simp only [List.foldr_cons, ih, List.Encoding.encode_cons, List.Encoding.foldr_cons]
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
      = List.foldr (β := A →𝒒 C) (fun y k ↦ .mk (fun x ↦ cons x y (k x))) (.mk nil) (f x) x := by
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

@[fun_prop]
lemma isHom_getElem?
    {f : A → List B} (hf : IsHom f)
    {g : A → ℕ} (hg : IsHom g)
    : IsHom (fun x ↦ (f x)[g x]?) := by
  have {x} : (f x)[g x]?
           = List.foldr
              (fun x k ↦ .mk fun i ↦ Nat.casesOn i (.some x) k)
              (.mk fun _ ↦ .none : ℕ →𝒒 Option B)
              (f x)
              (g x) := by
    generalize g x = n
    induction f x generalizing n with
    | nil =>
      simp only [
        List.length_nil, not_lt_zero', not_false_eq_true, getElem?_neg,
        List.foldr_nil, QuasiBorelHom.coe_mk]
    | cons head tail ih =>
      cases n with
      | zero =>
        simp only [
          List.length_cons, lt_add_iff_pos_left, add_pos_iff, zero_lt_one,
          or_true, getElem?_pos, List.getElem_cons_zero, List.foldr_cons,
          QuasiBorelHom.coe_mk, Nat.rec_zero]
      | succ n =>
        simp only [
          List.getElem?_cons_succ, ih,
          List.foldr_cons, QuasiBorelHom.coe_mk]
  simp only [this]
  fun_prop

@[fun_prop]
lemma isHom_length : IsHom (List.length : List A → ℕ) := by
  have hcons : IsHom fun p : A × ℕ ↦ p.2.succ := by
    fun_prop
  have hfold : IsHom (List.foldr (fun _ n ↦ n.succ) 0) :=
    isHom_foldr (A := A) (B := ℕ) hcons 0
  have hfun :
      (fun xs : List A ↦ List.foldr (fun _ n ↦ n.succ) 0 xs)
        = List.length := by
    funext xs
    induction xs with
    | nil => simp
    | cons head tail ih => simp [ih]
  simpa [hfun] using hfold

omit [QuasiBorelSpace B] in
private lemma getOption_eq_some_get
    {xs : List B} {n : ℕ} (h : n < xs.length)
    : xs[n]? = some (xs[n]'(h)) := by
  classical
  revert n h
  induction xs with
  | nil =>
      intro n h
      cases h
  | cons y ys ih =>
      intro n h
      cases n with
      | zero =>
          simp
      | succ n =>
          have h' : n < ys.length := by
            simpa [List.length_cons, Nat.succ_lt_succ_iff] using h
          simp [ih h']

section Inhabited

variable [Inhabited B]

omit [QuasiBorelSpace B] in
private lemma getOption_getD_eq_get
    {xs : List B} {n : ℕ} (h : n < xs.length)
    : (xs[n]?).getD (default : B) = xs[n]'(h) := by
  classical
  have : xs[n]? = some (xs[n]'(h)) := getOption_eq_some_get (B := B) (xs := xs) (n := n) h
  simp [Option.getD, this]

lemma isHom_get
    {f : A → List B} (hf : IsHom f)
    {g : A → ℕ} (hg : IsHom g)
    (h : ∀ x, g x < (f x).length)
    : IsHom (fun x ↦ have := h x; (f x)[g x]) := by
  dsimp only [Lean.Elab.WF.paramLet]
  classical
  have hoption : IsHom (fun x ↦ (f x)[g x]?) :=
    isHom_getElem? hf hg
  have hconst : IsHom fun (_ : A) ↦ (default : B) := by
    fun_prop
  have hgetD : IsHom (fun x ↦ ((f x)[g x]?).getD (default : B)) :=
    QuasiBorelSpace.Option.isHom_getD hoption hconst
  have hrepr :
      (fun x ↦ (f x)[g x]'(h x))
        = fun x ↦ ((f x)[g x]?).getD (default : B) := by
    funext x
    simp [getOption_getD_eq_get (B := B) (xs := f x) (n := g x) (h := h x)]
  simpa [hrepr] using hgetD

end Inhabited

@[fun_prop]
lemma isHom_ofFn
    {n} {f : A → Fin n → B} (hf : IsHom fun (x, y) ↦ f x y)
    : IsHom (fun x ↦ List.ofFn (f x)) := by
  classical
  revert f
  induction n with
  | zero =>
      intro f hf
      simp
  | succ n ih =>
      intro f hf
      have hhead : IsHom (fun x ↦ f x (0 : Fin (n + 1))) := by
        fun_prop
      have hf' : IsHom (fun p : A × Fin n ↦ f p.1 (Fin.succ p.2)) := by
        fun_prop
      have htail : IsHom (fun x ↦ List.ofFn fun i : Fin n ↦ f x (Fin.succ i)) :=
        ih (f := fun x i => f x (Fin.succ i)) hf'
      have hcons : IsHom
          (fun x ↦ f x 0 :: List.ofFn fun i : Fin n ↦ f x (Fin.succ i)) :=
        isHom_cons' (A := A) (B := B) hhead htail
      simpa [List.ofFn_succ] using hcons

instance
    [MeasurableSpace A] [MeasurableQuasiBorelSpace A]
    : MeasurableQuasiBorelSpace (List A) where
  isHom_iff_measurable φ := by
    simp only [isHom_to_lift, isHom_iff_measurable, MeasureTheory.List.measurable_to_encode]

/--
Converts a sequence of measures into a measure of sequences, where each element
is drawn from an element of the original sequence.
-/
@[simp]
noncomputable def sequence : List (ProbabilityMeasure A) → ProbabilityMeasure (List A)
  | [] => .unit []
  | μ :: μs => .bind (fun x ↦ .map (x :: ·) (sequence μs)) μ

/-- Lifting integration to sequences. -/
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
