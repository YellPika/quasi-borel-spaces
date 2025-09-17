import QuasiBorelSpaces.Prod

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
  /-- The underlying index type. -/
  Index : Type
  /-- The underlying index type is countable. -/
  [countable_index : Countable Index]
  /-- Each index represents some `I`. -/
  embed : Index → I
  /-- Obtains the index of the underlying variable, given the intended input. -/
  index : ℝ → Index
  /-- The family of variables. -/
  var : (i : Index) → ℝ → P (embed i)
  /-- Each variable is, in fact, a variable. -/
  isVar_var : ∀i, IsVar (var i)
  /-- The index function is measurable. -/
  measurable_index : Measurable[_, ⊤] index

namespace Var

attribute [instance] countable_index

/--
Since every `Var` represents a variable, each `Var` induces a function
`ℝ → Σi, P i`.
-/
def apply (x : Var I P) (r : ℝ) : Sigma P :=
  ⟨x.embed (x.index r), x.var (x.index r) r⟩

@[simp]
lemma apply_mk
    {J : Type} [Countable J]
    {f : J → I} {i : ℝ → J} {φ : (i : J) → ℝ → P (f i)} {r : ℝ}
    (hφ : ∀ i, IsVar (φ i)) (hi : Measurable[_, ⊤] i)
    : apply ⟨J, f, i, φ, hφ, hi⟩ r = ⟨f (i r), φ (i r) r⟩ :=
  rfl

instance : CoeFun (Var I P) (fun _ ↦ ℝ → Sigma P) where
  coe := apply

/-- The constant variable. -/
def const (x : Sigma P) : Var I P where
  Index := Unit
  embed _ := x.1
  index _ := ()
  var _ _ := x.2
  isVar_var := by simp only [isVar_const, implies_true]
  measurable_index := measurable_const

@[simp]
lemma const_apply (x : Sigma P) (r : ℝ) : const x r = x := rfl

/-- Composition under measurable functions. -/
def comp {f : ℝ → ℝ} (hf : Measurable f) (x : Var I P) : Var I P where
  Index := x.Index
  embed := x.embed
  index r := x.index (f r)
  var i r := x.var i (f r)
  isVar_var i := isVar_comp hf (x.isVar_var i)
  measurable_index := Measurable.comp' x.measurable_index hf

@[simp]
lemma comp_apply
    {f : ℝ → ℝ} (hf : Measurable f)
    (x : Var I P) (r : ℝ)
    : comp hf x r = x (f r) :=
  rfl

/-- Gluing of a countable number of variables. -/
def cases {ix : ℝ → ℕ} (hix : Measurable ix) (φ : ℕ → Var I P) : Var I P where
  Index := (n : ℕ) × (φ n).Index
  embed x := (φ x.1).embed x.2
  index r := ⟨ix r, (φ (ix r)).index r⟩
  var i r := (φ i.1).var i.2 r
  isVar_var i := (φ i.1).isVar_var i.2
  measurable_index := by
    let : MeasurableSpace ((n : ℕ) × (φ n).Index) := ⊤
    apply MeasureTheory.measurable_cases (f := fun n r ↦
        (⟨n, (φ n).index r⟩ : (n : ℕ) × (φ n).Index))
    · exact hix
    · intro i
      apply Measurable.comp'
      · apply measurable_from_top
      · apply measurable_index

@[simp]
lemma cases_apply
    {ix : ℝ → ℕ} (hix : Measurable ix)
    (φ : ℕ → Var I P) (r : ℝ)
    : cases hix φ r = φ (ix r) r :=
  rfl

/-- Normal `QuasiBorelSpace.Var`s can be pushed 'inside' a `Var`. -/
def distrib {φ₁ : ℝ → A} (hφ₁ : IsVar φ₁) (φ₂ : Var I P) : Var I (fun i ↦ A × P i) where
  Index := φ₂.Index
  embed := φ₂.embed
  index := φ₂.index
  var i r := (φ₁ r, φ₂.var i r)
  isVar_var i := ⟨hφ₁, φ₂.isVar_var i⟩
  measurable_index := φ₂.measurable_index

@[simp]
lemma distrib_apply
    {φ₁ : ℝ → A} (hφ₁ : IsVar φ₁) (φ₂ : Var I P) (r : ℝ)
    : apply (distrib hφ₁ φ₂) r = ⟨(φ₂ r).1, φ₁ r, (φ₂ r).2⟩ :=
  rfl

end Var

@[simps]
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

@[fun_prop, simp]
lemma isHom_inj (i) : IsHom (⟨i, ·⟩ : P i → Sigma P) := by
  intro φ hφ
  simp only [IsVar_def]
  use {
    Index := Unit
    embed _ := i
    index _ := ()
    var _ := φ
    isVar_var _ := hφ
    measurable_index := by simp only [measurable_const]
  }
  simp only [Var.apply_mk, implies_true]

@[fun_prop]
lemma isHom_inj' {i} {f : A → P i} (hf : IsHom f) : IsHom (fun x ↦ ⟨i, f x⟩ : A → Sigma P) := by
  apply isHom_comp
  · exact isHom_inj i
  · exact hf

lemma isHom_inj_countable
    [Countable I] [QuasiBorelSpace I] [DiscreteQuasiBorelSpace I]
    {f : A → I} (hf : IsHom f)
    {g : (i : I) → A → P i} (hg : ∀ i, IsHom (g i))
    : IsHom (fun x ↦ (⟨f x, g (f x) x⟩ : Sigma P)) := by
  apply isHom_cases (ix := f) (f := fun i x ↦ (⟨i, g i x⟩ : Sigma P))
  · fun_prop
  · fun_prop

lemma isHom_elim {f : Sigma P → A} (hf : ∀ i, IsHom (fun x ↦ f ⟨i, x⟩)) : IsHom f := by
  intro φ hφ
  choose φ hφ₀ using hφ
  rcases φ with ⟨J, emb, ix, var, hvar, hix⟩
  simp only [Var.apply_mk] at hφ₀
  conv => enter [1, x]; rw [hφ₀]
  apply isVar_cases (ix := ix) (φ := fun i x ↦ f ⟨emb i, var i x⟩)
  · apply hix
  · intro j
    apply hf
    apply hvar

lemma isHom_elim'
    {f : ∀ i, P i → B} (hf : ∀ i, IsHom (f i))
    {g : A → (i : I) × P i} (hg : IsHom g)
    : IsHom (fun x ↦ f (g x).1 (g x).2) := by
  apply isHom_comp' (f := fun x : Sigma P ↦ (f x.1 x.2 : B)) (g := g)
  · exact isHom_elim hf
  · exact hg

@[fun_prop, simp]
lemma isHom_fst [QuasiBorelSpace I] : IsHom (Sigma.fst : Sigma P → I) := by
  intro φ ⟨ψ, hψ⟩
  simp only [hψ]
  rcases ψ with ⟨Index, embed, index, var, isVar_var, measurable_index⟩
  simp only [Var.apply_mk]
  apply isVar_cases (ix := index) (φ := fun n r ↦ embed n)
  · exact measurable_index
  · simp only [isVar_const, implies_true]

lemma isHom_distrib : IsHom (fun x : A × Sigma P ↦ (⟨x.2.1, x.1, x.2.2⟩ : (i : I) × A × P i)) := by
  intro φ ⟨hφ₁, ψ, hφ₂⟩
  exists Var.distrib hφ₁ ψ
  intro r
  simp only [Var.distrib_apply]
  simp only at hφ₂
  rw [hφ₂]

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
  apply isHom_inj'
  apply hg

end QuasiBorelSpace.Sigma
