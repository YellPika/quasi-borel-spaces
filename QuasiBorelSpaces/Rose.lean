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

private def foldAlgHom
    (mk : A → B → List C → C)
    (hmk : IsHom fun (x, y, z) ↦ mk x y z)
    : B → List (A →𝒒 C) → A →𝒒 C :=
  fun b ks ↦
    QuasiBorelHom.mk
      (fun a ↦ mk a b (List.map (fun k : A →𝒒 C ↦ k a) ks)) (by
        fun_prop)

private lemma map_congr'
    {α β : Type*} {l : List α} {f g : α → β}
    (h : ∀ x ∈ l, f x = g x) : List.map f l = List.map g l := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      have hx : f x = g x := by
        exact h x (by simp)
      have hxs : ∀ y ∈ xs, f y = g y := by
        intro y hy
        exact h y (by simp [hy])
      simp [hx, ih hxs]

private lemma fold_pointwise
    (mk : A → B → List C → C)
    (hmk : IsHom fun (x, y, z) ↦ mk x y z)
    (t : Rose B) (a : A)
    : Rose.fold (mk a) t
      =
        (Rose.Encoding.fold
            (A := B)
            (mk := foldAlgHom mk hmk)
            (Rose.Encoding.encode (A := B) t) : A →𝒒 C) a := by
  classical
  induction t with
  | mk label children ih =>
      have hchild :
          List.map (fun child ↦ Rose.fold (mk a) child) children
            = List.map
                (fun child ↦
                  (Rose.Encoding.fold
                      (A := B)
                      (mk := foldAlgHom mk hmk)
                      (Rose.Encoding.encode (A := B) child) : A →𝒒 C) a)
                children := by
        refine map_congr' ?_
        intro child hmem
        simpa using ih child hmem
      have hchild' :
          List.map
              ((fun k : A →𝒒 C ↦ k a) ∘
                Rose.Encoding.fold (A := B) (mk := foldAlgHom mk hmk) ∘
                Rose.Encoding.encode (A := B))
              children
            = List.map
                (fun child ↦
                  (Rose.Encoding.fold
                      (A := B)
                      (mk := foldAlgHom mk hmk)
                      (Rose.Encoding.encode (A := B) child) : A →𝒒 C) a)
                children := by
        simp [Function.comp]
      simp [Rose.fold.eq_1, Rose.Encoding.encode_mk, Rose.Encoding.fold_mk,
        foldAlgHom, List.map_map, hchild, hchild']

private lemma fold_as_quasiBorelHom
    (mk : A → B → List C → C)
    (hmk : IsHom fun (x, y, z) ↦ mk x y z)
    (f : A → Rose B)
    : (fun x ↦ Rose.fold (mk x) (f x))
      =
        (fun x ↦
          (Rose.Encoding.fold
              (A := B)
              (mk := foldAlgHom mk hmk)
              (Rose.Encoding.encode (A := B) (f x)) : A →𝒒 C) x) := by
  funext x
  simpa using fold_pointwise mk hmk (f x) x

@[fun_prop]
lemma isHom_fold'
    {mk : A → B → List C → C} (hmk : IsHom fun (x, y, z) ↦ mk x y z)
    {f : A → Rose B} (hf : IsHom f)
    : IsHom (fun x ↦ Rose.fold (mk x) (f x)) := by
  classical
  have hrewrite := fold_as_quasiBorelHom (A := A) (B := B) (C := C) mk hmk f
  have h_alg :
      IsHom (fun p : B × List (A →𝒒 C) ↦
        foldAlgHom mk hmk p.1 p.2) := by
    dsimp [foldAlgHom]
    fun_prop
  have h_fold :
      IsHom (Rose.Encoding.fold
              (foldAlgHom mk hmk)) := by
    simpa [foldAlgHom] using Rose.Encoding.isHom_fold (A := B) (B := A →𝒒 C)
      (mk := foldAlgHom mk hmk) (hmk := by simpa using h_alg)
  have h_apply :
      IsHom (fun x ↦
        (Rose.Encoding.fold
            (A := B)
            (mk := foldAlgHom mk hmk)
            (Rose.Encoding.encode (A := B) (f x)) : A →𝒒 C) x) := by
    fun_prop
  simpa [hrewrite] using h_apply

@[simp, fun_prop]
lemma isHom_label : IsHom (fun t : Rose A ↦ t.label) := by
  have h : IsHom (fun e : Rose.Encoding A ↦ e.2 []) := by
    fun_prop
  have hencode : IsHom (Rose.Encoding.encode (A := A)) := isHom_encode (A := A)
  have hcomp := isHom_comp' h hencode
  have hfun : (fun t : Rose A ↦ (Rose.Encoding.encode t).2 [])
      = fun t ↦ t.label := by
    funext t
    cases t with
    | mk label children =>
        simp [Rose.Encoding.encode_mk, Rose.Encoding.mk]
  simpa [hfun] using hcomp

private def childrenFoldAlg (x : C) (xs : List (Rose C × List (Rose C)))
    : Rose C × List (Rose C) :=
  let children := List.map Prod.fst xs
  (Rose.mk x children, children)

section
omit [QuasiBorelSpace C]
private lemma fold_children_eq
    (t : Rose C)
    : Rose.Encoding.fold (childrenFoldAlg (C := C)) (Rose.Encoding.encode t)
        = (t, t.children) := by
  induction t with
  | mk label children ih =>
      have hxs :
          List.map
              (Rose.Encoding.fold (childrenFoldAlg (C := C))
                ∘ Rose.Encoding.encode (A := C))
              children
            = List.map (fun child ↦ (child, child.children)) children := by
        refine map_congr' ?_
        intro child hmem
        simpa using ih child hmem
      have hchildren :
          List.map (Prod.fst ∘ fun child ↦ (child, child.children)) children
            = children := by
        unfold Function.comp
        simp
      simp [Rose.Encoding.encode_mk, Rose.Encoding.fold_mk, childrenFoldAlg,
        hxs, List.map_map, hchildren]
end

@[simp, fun_prop]
lemma isHom_children : IsHom (fun t : Rose C ↦ t.children) := by
  have hfAlg :
      IsHom (fun p : C × List (Rose C × List (Rose C)) ↦
        childrenFoldAlg (C := C) p.1 p.2) := by
    dsimp [childrenFoldAlg]
    fun_prop
  have hfoldRaw : IsHom (Rose.Encoding.fold (childrenFoldAlg (C := C))) := by
    simpa[childrenFoldAlg] using Rose.Encoding.isHom_fold
      (A := C) (B := Rose C × List (Rose C))
      (mk := childrenFoldAlg (C := C)) (hmk := by simpa [childrenFoldAlg] using hfAlg)
  have hprod : IsHom (fun p : Rose C × List (Rose C) ↦ p.2) := by
    fun_prop
  have hfold :
      IsHom (fun e : Rose.Encoding C ↦
        (Rose.Encoding.fold (childrenFoldAlg (C := C)) e).2) :=
    isHom_comp' hprod hfoldRaw
  have hencode : IsHom (Rose.Encoding.encode (A := C)) := isHom_encode (A := C)
  have hcomp := isHom_comp' hfold hencode
  have hfun : (fun t : Rose C ↦
        (Rose.Encoding.fold (childrenFoldAlg (C := C)) (Rose.Encoding.encode t)).2)
      = fun t ↦ t.children := by
    funext t
    simp [fold_children_eq]
  simpa [hfun] using hcomp

private def bindFoldAlg (f : B → Rose C) (b : B) (zs : List (Rose C)) : Rose C :=
  let t := f b
  Rose.mk t.label (List.foldr (fun child acc ↦ child :: acc) zs t.children)

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
