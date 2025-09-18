import QuasiBorelSpaces.Defs
import QuasiBorelSpaces.MeasureTheory.Pack

open scoped MeasureTheory

namespace QuasiBorelSpace

variable
  {A B C : Type*} [QuasiBorelSpace A] [QuasiBorelSpace B] [QuasiBorelSpace C]
  {I : Type*} [Countable I]

@[simp]
lemma isVar_iff_measurable
    [MeasurableSpace A] [MeasurableQuasiBorelSpace A]
    (φ : ℝ → A)
    : IsVar φ ↔ Measurable φ :=
  MeasurableQuasiBorelSpace.isVar_iff_measurable φ

lemma isHom_of_measurable
    [MeasurableSpace A] [MeasurableQuasiBorelSpace A]
    [MeasurableSpace B] [MeasurableQuasiBorelSpace B]
    (f : A → B) (hf : Measurable f)
    : IsHom f := by
  intro φ hφ
  simp only [isVar_iff_measurable] at ⊢ hφ
  fun_prop

lemma isVar_cases
    {ix : ℝ → I} {φ : I → ℝ → A}
    (hix : Measurable[_, ⊤] ix) (hφ : ∀ n, IsVar (φ n))
    : IsVar (fun r ↦ φ (ix r) r) := by
  have hI : Nonempty I := ⟨ix 0⟩

  have ⟨k, hk⟩ := Countable.exists_injective_nat I
  have hk' : ∀i, k.invFun (k i) = i := by
    apply Function.leftInverse_invFun
    apply hk

  have hix' : Measurable (fun x ↦ k (ix x)) := by
    apply Measurable.comp'
    · apply measurable_from_top
    · apply hix

  have hφk (n) : IsVar (φ (Function.invFun k n)) := by
    simp only [hφ]

  have := isVar_cases' hix' hφk
  simp only [hk'] at this
  apply this

@[simp]
lemma isHom_iff_isVar (f : ℝ → A) : IsHom f ↔ IsVar f := by
  apply Iff.intro
  · intro hf
    apply hf
    apply measurable_id
  · intro hf φ hφ
    apply isVar_comp hφ hf

@[fun_prop, simp]
lemma isHom_id : IsHom (A := A) id := by
  intro φ hφ
  exact hφ

@[fun_prop, simp]
lemma isHom_id' : IsHom (fun x : A ↦ x) := by
  intro φ hφ
  exact hφ

@[fun_prop]
lemma isHom_comp
    {f : B → C} (hf : IsHom f)
    {g : A → B} (hg : IsHom g)
    : IsHom (f ∘ g) := by
  intro φ hφ
  apply hf
  apply hg
  apply hφ

@[fun_prop]
lemma isHom_comp'
    {f : B → C} (hf : IsHom f)
    {g : A → B} (hg : IsHom g)
    : IsHom (fun x ↦ f (g x)) := by
  exact isHom_comp hf hg

@[fun_prop, simp]
lemma isHom_const (x : B) : IsHom (fun _ : A ↦ x) := by
  intro _ _
  apply isVar_const

lemma isHom_cases
    {ix : A → I} {f : I → A → B}
    (hix : IsHom[_, default] ix) (hf : ∀ n, IsHom (f n))
    : IsHom (fun x ↦ f (ix x) x) := by
  intro φ hφ
  apply isVar_cases (ix := fun x ↦ ix (φ x)) (φ := fun n x ↦ f n (φ x))
  · specialize hix hφ
    simp only [default_IsVar] at hix
    exact hix
  · intro n
    apply hf
    apply hφ

@[simp]
lemma isHom_of_discrete_countable
    [MeasurableSpace A] [DiscreteQuasiBorelSpace A] [Countable A]
    (f : A → B) : IsHom f := by
  apply isHom_cases (ix := fun x ↦ x) (f := fun x _ ↦ f x)
  · intro φ hφ
    simp only [isVar_iff_measurable, default_IsVar] at ⊢ hφ
    intro X hX
    apply hφ
    apply MeasurableSet.of_discrete
  · fun_prop

@[simp]
lemma isHom_to_subsingleton [Subsingleton B] (f : A → B) : IsHom f := by
  intro φ hφ
  have : ∀r, f (φ r) = f (φ 0) := by subsingleton
  simp only [this, isVar_const]

lemma isHom_to_lift
    {A} (f : A → B) (g : C → A)
    : IsHom[_, lift f] g ↔ IsHom (fun x ↦ f (g x)) := by
  rfl

lemma isHom_of_lift {A} (f : A → B) : IsHom[lift f, _] f := by
  intro φ hφ
  apply hφ

@[simp, fun_prop]
lemma isHom_unpack
    [Nonempty A] [MeasurableSpace A] [MeasurableQuasiBorelSpace A] [StandardBorelSpace A]
    : IsHom (MeasureTheory.unpack (A := A)) := by
  simp only [isHom_iff_isVar, isVar_iff_measurable, MeasureTheory.measurable_unpack]

lemma isHom_cast
    {B : Type _} [instB : QuasiBorelSpace B]
    {C : Type _} [instC : QuasiBorelSpace C]
    {eq : B = C} (heq : ∀ φ, instB.IsVar φ ↔ instC.IsVar fun x ↦ cast eq (φ x))
    (f : A → B)
    : IsHom (fun x ↦ cast eq (f x)) ↔ IsHom f := by
  subst eq
  have : instB = instC := by
    ext
    apply heq
  subst this
  rfl

end QuasiBorelSpace
