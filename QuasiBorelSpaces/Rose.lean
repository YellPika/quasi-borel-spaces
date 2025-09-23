import QuasiBorelSpaces.Hom
import QuasiBorelSpaces.Rose.Encoding
import QuasiBorelSpaces.List
import QuasiBorelSpaces.Option
import QuasiBorelSpaces.Nat
import QuasiBorelSpaces.Pi
import QuasiBorelSpaces.ProbabilityMeasure
import QuasiBorelSpaces.Sigma

variable {A B C : Type*} [QuasiBorelSpace A] [QuasiBorelSpace B] [QuasiBorelSpace C]

namespace Rose.Encoding

open QuasiBorelSpace

@[simp, fun_prop]
lemma isHom_mk : IsHom (fun x : A × List (Rose.Encoding A) ↦ mk x.1 x.2) := by
  unfold mk
  apply isHom_cases (f := fun s (x : A × _) ↦ (⟨s, (mk x.1 x.2).2⟩ : Encoding _))
  · let : QuasiBorelSpace (Rose Unit) := default
    let : MeasurableSpace (Rose Unit) := ⊤
    fun_prop
  · intro t
    simp only [mk]
    apply Sigma.isHom_mk'
    simp only [Pi.isHom_iff]
    intro is
    cases is with
    | nil => simp only [Prod.isHom_fst]
    | cons head tail => fun_prop

@[fun_prop]
lemma isHom_fold
      {mk : A → List B → B} (hmk : IsHom fun (x, y) ↦ mk x y)
    : IsHom (fold mk) := by
  apply Sigma.isHom_elim
  intro t
  induction t with | mk label children ih =>
  have {k : List ℕ → A}
      : fold mk ⟨{ label := label, children := children }, k⟩
      = fold mk (Encoding.mk (k []) (List.ofFn fun i ↦ ⟨children[i], fun is ↦ k (i :: is)⟩)) := by
    simp only [
      Encoding.mk, Fin.getElem_fin, List.map_ofFn, List.getElem?_ofFn,
      Option.map_dif, dite_eq_ite, fold, List.length_ofFn, Fin.coe_cast,
      List.getElem_ofFn, Fin.eta, Function.comp_apply, Fin.is_lt, ↓reduceIte,
      Option.getD_some]
    nth_rw 1 [fold]
    simp only [Fin.getElem_fin]
  simp only [this, Fin.getElem_fin, fold_mk, List.map_ofFn]
  have : IsHom fun (x : List ℕ → A) ↦
      (List.ofFn (fold mk ∘ fun i ↦ ⟨children[↑i], fun is ↦ x (↑i :: is)⟩)) := by
    apply List.isHom_ofFn
    simp only [Fin.getElem_fin, Function.comp_apply]
    apply isHom_cases
        (ix := fun x : (List ℕ → A) × Fin children.length ↦ x.2)
        (f := fun n x ↦ fold mk ⟨children[n], fun is ↦ x.1 (↑x.2 :: is)⟩)
    · fun_prop
    · intro n
      specialize ih children[n] (by simp only [Fin.getElem_fin, List.getElem_mem])
      apply isHom_comp' ih
      simp only [Pi.isHom_iff]
      intro i
      apply isHom_cases
          (ix := fun x : (List ℕ → A) × Fin children.length ↦ (↑x.2 :: i))
          (f := fun is x ↦ x.1 is)
      · fun_prop
      · fun_prop
  fun_prop

end Rose.Encoding

namespace QuasiBorelSpace.Rose

instance : QuasiBorelSpace (Rose A) := lift Rose.Encoding.encode

@[simp, fun_prop]
lemma isHom_encode : IsHom (Rose.Encoding.encode (A := A)) := by
  apply isHom_of_lift

@[fun_prop]
lemma isHom_mk : IsHom (fun x : A × List (Rose A) ↦ Rose.mk x.1 x.2) := by
  simp only [isHom_to_lift, Rose.Encoding.encode_mk]
  fun_prop

lemma isHom_cons'
    {f : A → B} (hf : IsHom f)
    {g : A → List (Rose B)} (hg : IsHom g)
    : IsHom (fun x ↦ Rose.mk (f x) (g x)) := by
  fun_prop

@[local fun_prop]
lemma isHom_fold
    {mk : A → List B → B} (hmk : IsHom fun (x, xs) ↦ mk x xs)
    : IsHom (Rose.fold mk) := by
  have : Rose.fold mk = fun xs ↦ Rose.Encoding.fold mk (.encode xs) := by
    ext t
    induction t with | mk label children ih =>
    simp only [Rose.fold.eq_1, Rose.Encoding.encode_mk, Rose.Encoding.fold_mk, List.map_map]
    congr 1
    simp only [List.map_inj_left, Function.comp_apply]
    grind
  rw [this]
  fun_prop

@[fun_prop]
lemma isHom_fold'
    {mk : A → B → List C → C} (hmk : IsHom fun (x, y, z) ↦ mk x y z)
    {f : A → Rose B} (hf : IsHom f)
    : IsHom (fun x ↦ Rose.fold (mk x) (f x)) := by
  -- Approach: see QuasiBorelSpace.List.isHom_foldr'
  sorry

lemma isHom_bind
    {f : A → B → Rose C} (hf : IsHom fun (x, y) ↦ f x y)
    {g : A → Rose B} (hg : IsHom g)
    : IsHom (fun x ↦ Rose.bind (f x) (g x)) := by
  -- Approach:
  -- 1. Show `Rose.bind (f x) (g x) = Rose.fold ? (g x) (f x)`
  -- 2. Show `IsHom fun x ↦ ?`
  -- 3. Apply `fun_prop`
  sorry

end QuasiBorelSpace.Rose
