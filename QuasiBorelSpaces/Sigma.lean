import QuasiBorelSpaces.Prod
import QuasiBorelSpaces.MeasureTheory.Sigma
import QuasiBorelSpaces.OmegaCompletePartialOrder.Sigma

/-!
# Small Coproducts of Quasi-Borel Spaces

This file defines small coproducts of quasi-borel spaces by giving a
`QuasiBorelSpace` instance for the `Σ` type.

See [HeunenKSY17], Proposition 17.
-/

open scoped MeasureTheory

namespace QuasiBorelSpace.Sigma

variable
  {I : Type*} {P : I → Type*} [∀ i, QuasiBorelSpace (P i)]
  {J : Type*} {Q : J → Type*} [∀ j, QuasiBorelSpace (Q j)]
  {A B C : Type*} [QuasiBorelSpace A] [QuasiBorelSpace B] [QuasiBorelSpace C]

/--
Represents a variable for a Σ-type. Intuitively, a variable in `Σi, P i` is a
gluing of a countable number of variables, each in some `P i`.
-/
structure Var (I : Type*) (P : I → Type*) [∀ i, QuasiBorelSpace (P i)] where
  /-- Each index represents some `I`. -/
  embed : ℕ → I
  /-- Obtains the index of the underlying variable, given the intended input. -/
  index : ℝ → ℕ
  /-- The family of variables. -/
  var : (i : ℕ) → ℝ → P (embed i)
  /-- Each variable is, in fact, a variable. -/
  isHom_var : ∀i, IsHom (var i)
  /-- The index function is measurable. -/
  measurable_index : Measurable[_, ⊤] index

namespace Var

attribute [fun_prop] measurable_index

/--
Since every `Var` represents a variable, each `Var` induces a function
`ℝ → Σi, P i`.
-/
def apply (x : Var I P) (r : ℝ) : Sigma P :=
  ⟨x.embed (x.index r), x.var (x.index r) r⟩

@[simp]
lemma apply_mk
    {f : ℕ → I} {i : ℝ → ℕ} {φ : (i : ℕ) → ℝ → P (f i)} {r : ℝ}
    (hφ : ∀ i, IsHom (φ i)) (hi : Measurable[_, ⊤] i)
    : apply ⟨f, i, φ, hφ, hi⟩ r = ⟨f (i r), φ (i r) r⟩ :=
  rfl

/-- A `Var` can be constructed from any `Encodable` index type. -/
def mk'
    (Index : Type*) [Encodable Index] (embed : Index → I) (index : ℝ → Index)
    (var : (i : Index) → ℝ → P (embed i)) (isHom_var : ∀ i, IsHom (var i))
    (measurable_index : Measurable[_, ⊤] index)
    : Var I P where
  embed n := embed ((Encodable.decode₂ Index n).getD (index 0))
  index r := Encodable.encode (index r)
  var i r := var _ r
  isHom_var i := isHom_var _
  measurable_index := by
    apply Measurable.comp'
    · apply measurable_from_top
    · exact measurable_index

@[simp]
lemma apply_mk'
    {J : Type*} [Encodable J]
    {f : J → I} {i : ℝ → J} {φ : (i : J) → ℝ → P (f i)} {r : ℝ}
    (hφ : ∀ i, IsHom (φ i)) (hi : Measurable[_, ⊤] i)
    : apply (mk' J f i φ hφ hi) r = ⟨f (i r), φ (i r) r⟩ := by
  simp only [mk', apply_mk, Sigma.mk.injEq, Encodable.decode₂_encode, Option.getD_some, true_and]
  rw [Encodable.decode₂_encode]
  simp only [Option.getD_some, heq_eq_eq]

instance : CoeFun (Var I P) (fun _ ↦ ℝ → Sigma P) where
  coe := apply

/-- The constant variable. -/
def const (x : Sigma P) : Var I P := mk'
  (Index := Unit)
  (embed := fun _ ↦ x.1)
  (index := fun _ ↦ ())
  (var := fun _ _ ↦ x.2)
  (isHom_var := by simp only [isHom_const, implies_true])
  (measurable_index := measurable_const)

@[simp]
lemma const_apply (x : Sigma P) (r : ℝ) : const x r = x := rfl

/-- Composition under measurable functions. -/
def comp {f : ℝ → ℝ} (hf : Measurable f) (x : Var I P) : Var I P where
  embed := x.embed
  index r := x.index (f r)
  var i r := x.var i (f r)
  isHom_var i := by
    apply isHom_comp'
    · apply x.isHom_var
    · simp only [isHom_ofMeasurableSpace, hf]
  measurable_index := Measurable.comp' x.measurable_index hf

@[simp]
lemma comp_apply
    {f : ℝ → ℝ} (hf : Measurable f)
    (x : Var I P) (r : ℝ)
    : comp hf x r = x (f r) :=
  rfl

/-- Gluing of a countable number of variables. -/
def cases {ix : ℝ → ℕ} (hix : Measurable ix) (φ : ℕ → Var I P) : Var I P := mk'
  (Index := ℕ × ℕ)
  (embed := fun x ↦ (φ x.1).embed x.2)
  (index := fun r ↦ ⟨ix r, (φ (ix r)).index r⟩)
  (var := fun i r ↦ (φ i.1).var i.2 r)
  (isHom_var := fun i ↦ (φ i.1).isHom_var i.2)
  (measurable_index := by
    let : MeasurableSpace (ℕ × ℕ) := ⊤
    apply MeasureTheory.measurable_cases (f := fun n r ↦
        (⟨n, (φ n).index r⟩ : ℕ × ℕ))
    · exact hix
    · intro i
      apply Measurable.comp'
      · apply measurable_from_top
      · apply measurable_index)

@[simp]
lemma cases_apply
    {ix : ℝ → ℕ} (hix : Measurable ix)
    (φ : ℕ → Var I P) (r : ℝ)
    : cases hix φ r = φ (ix r) r := by
  simp only [cases, apply_mk']
  rfl

/-- Normal `QuasiBorelSpace.Var`s can be pushed 'inside' a `Var`. -/
def distrib {φ₁ : ℝ → A} (hφ₁ : IsHom φ₁) (φ₂ : Var I P) : Var I (fun i ↦ A × P i) where
  embed := φ₂.embed
  index := φ₂.index
  var i r := (φ₁ r, φ₂.var i r)
  isHom_var i := by simp only [Prod.isHom_iff, hφ₁, φ₂.isHom_var i, and_self]
  measurable_index := φ₂.measurable_index

@[simp]
lemma distrib_apply
    {φ₁ : ℝ → A} (hφ₁ : IsHom φ₁) (φ₂ : Var I P) (r : ℝ)
    : apply (distrib hφ₁ φ₂) r = ⟨(φ₂ r).1, φ₁ r, (φ₂ r).2⟩ :=
  rfl

instance [∀ i, LE (P i)] : LE (Var I P) where
  le φ₁ φ₂ := ∀x, apply φ₁ x ≤ apply φ₂ x

instance [∀ i, Preorder (P i)] : Preorder (Var I P) where
  le_refl φ x := by simp only [le_refl]
  le_trans φ₁ φ₂ φ₃ h₁ h₂ x := by
    apply le_trans
    · apply h₁
    · apply h₂

end Var

instance : QuasiBorelSpace (Σ i : I, P i) where
  IsVar φ := ∃ (ψ : Var I P), ∀r, φ r = ψ r
  isVar_const x := by
    use Var.const x
    simp only [Var.const_apply, implies_true]
  isVar_comp hf hφ := by
    rcases hφ with ⟨ψ, hψ⟩
    use ψ.comp hf
    simp only [hψ, Var.comp_apply, implies_true]
  isVar_cases' hindex hφ := by
    choose ψ hψ using hφ
    use Var.cases hindex ψ
    simp only [hψ, Var.cases_apply, implies_true]

@[local simp]
lemma isHom_def (φ : ℝ → (i : I) × P i) : IsHom φ ↔ ∃ (ψ : Var I P), ∀r, φ r = ψ r := by
  rw [← isVar_iff_isHom]
  rfl

@[fun_prop, simp]
lemma isHom_mk (i) : IsHom (⟨i, ·⟩ : P i → Sigma P) := by
  rw [QuasiBorelSpace.isHom_def]
  simp only [isHom_def]
  intro φ hφ
  use .mk'
    (Index := Unit)
    (embed := fun _ ↦ i)
    (index := fun _ ↦ ())
    (var := fun _ ↦ φ)
    (isHom_var := fun _ ↦ hφ)
    (measurable_index := by simp only [measurable_const])
  simp only [Var.apply_mk', implies_true]

@[fun_prop]
lemma isHom_mk' {i} {f : A → P i} (hf : IsHom f) : IsHom (fun x ↦ ⟨i, f x⟩ : A → Sigma P) := by
  fun_prop

lemma isHom_elim {f : Sigma P → A} (hf : ∀ i, IsHom (fun x ↦ f ⟨i, x⟩)) : IsHom f := by
  rw [QuasiBorelSpace.isHom_def]
  simp only [isHom_def]
  intro φ hφ
  choose φ hφ₀ using hφ
  rcases φ with ⟨emb, ix, var, hvar, hix⟩
  simp only [Var.apply_mk] at hφ₀
  conv => enter [1, x]; rw [hφ₀]
  apply isHom_cases (ix := ix) (f := fun i x ↦ f ⟨emb i, var i x⟩)
  · simp only [isHom_ofMeasurableSpace, hix]
  · intro j
    apply isHom_comp' (hf (emb j)) (hvar j)

lemma isHom_elim'
    {f : ∀ i, P i → B} (hf : ∀ i, IsHom (f i))
    {g : A → (i : I) × P i} (hg : IsHom g)
    : IsHom (fun x ↦ f (g x).1 (g x).2) := by
  apply isHom_comp' (f := fun x : Sigma P ↦ (f x.1 x.2 : B)) (g := g)
  · exact isHom_elim hf
  · exact hg

@[fun_prop, simp]
lemma isHom_fst [QuasiBorelSpace I] : IsHom (Sigma.fst : Sigma P → I) := by
  rw [QuasiBorelSpace.isHom_def]
  simp only [isHom_def, forall_exists_index]
  intro φ ψ hψ
  simp only [hψ]
  rcases ψ with ⟨embed, index, var, isHom_var, measurable_index⟩
  simp only [Var.apply_mk]
  apply isHom_cases (ix := index) (f := fun n r ↦ embed n)
  · simp only [isHom_ofMeasurableSpace, measurable_index]
  · simp only [isHom_const, implies_true]

@[fun_prop]
lemma isHom_snd : IsHom (Sigma.snd : (_ : I) × A → A) := by
  rw [QuasiBorelSpace.isHom_def]
  simp only [isHom_def, forall_exists_index]
  intro φ ψ hψ
  simp only [hψ]
  rcases ψ with ⟨embed, index, var, isHom_var, measurable_index⟩
  simp only [Var.apply_mk]
  apply isHom_cases (ix := index) (f := fun n r ↦ var n r)
  · simp only [isHom_ofMeasurableSpace, measurable_index]
  · fun_prop

lemma isHom_distrib : IsHom (fun x : A × Sigma P ↦ (⟨x.2.1, x.1, x.2.2⟩ : (i : I) × A × P i)) := by
  rw [QuasiBorelSpace.isHom_def]
  simp only [Prod.isHom_iff, isHom_def, and_imp, forall_exists_index]
  intro φ hφ ψ hψ
  exists Var.distrib hφ ψ
  intro r
  simp only [Var.distrib_apply]
  rw [hψ]

lemma isHom_distrib'
    {f : A × Sigma P → B} (hf : IsHom (fun x : (i : I) × A × P i ↦ f ⟨x.2.1, x.1, x.2.2⟩))
    : IsHom f := by
  apply isHom_comp'
      (f := fun x : (i : I) × A × P i ↦ f ⟨x.2.1, x.1, x.2.2⟩)
      (g := fun x : A × Sigma P ↦ ⟨x.2.1, x.1, x.2.2⟩)
  · exact hf
  · apply isHom_distrib

@[fun_prop]
lemma isHom_map
    {f : I → J}
    {g : ∀ i, P i → Q (f i)} (hg : ∀ i, IsHom (g i))
    : IsHom (Sigma.map f g) := by
  unfold Sigma.map
  apply isHom_elim
  intro i
  dsimp only
  fun_prop

instance
    [Countable I] [∀ i, MeasurableSpace (P i)] [∀ i, MeasurableQuasiBorelSpace (P i)]
    : MeasurableQuasiBorelSpace (Sigma P) where
  isHom_iff_measurable φ := by
    classical
    rw [isHom_def]
    apply Iff.intro
    · intro ⟨ψ, hψ⟩
      rw [←funext_iff] at hψ
      subst hψ
      apply MeasureTheory.measurable_cases
        (ix := ψ.index)
        (f := fun i r ↦ (⟨ψ.embed i, ψ.var i r⟩ : Sigma P))
      · fun_prop
      · intro i
        apply MeasureTheory.Sigma.measurable_mk'
        have := ψ.isHom_var i
        simp only [isHom_iff_measurable] at this
        exact this
    · intro h
      have := Encodable.ofCountable I
      have {i : {i : I // ∃r, (φ r).1 = i}} : Nonempty (P i.val) := by
        rcases i.property with ⟨r, hi⟩
        simp only [← hi]
        use (φ r).snd
      use .mk'
          {i : I // ∃r, (φ r).1 = i}
          Subtype.val
          (fun x ↦ ⟨(φ x).1, by grind⟩)
          (fun i r ↦ if h : (φ r).1 = i then h ▸ (φ r).2 else Classical.arbitrary _)
          ?_
          ?_
      · intro r
        rw [Var.apply_mk']
        simp only [↓reduceDIte]
      · intro ⟨i, hi⟩
        simp only [isHom_iff_measurable]
        apply MeasureTheory.measurable_dite
        · change Measurable fun x ↦ (φ x).fst ∈ ({i} : Set _)
          apply Measurable.comp'
          · simp only [measurable_mem]
            apply MeasurableSpace.measurableSet_top
          · fun_prop
        · apply MeasureTheory.Sigma.measurable_eq_rec
          simp only [Sigma.eta]
          fun_prop
        · fun_prop
      · intro _ _
        apply Measurable.subtype_mk
        · apply Measurable.comp'
          · simp only [MeasureTheory.Sigma.measurable_fst]
          · apply h
        · apply MeasurableSet.of_subtype_image
          apply MeasurableSpace.measurableSet_top

end QuasiBorelSpace.Sigma
