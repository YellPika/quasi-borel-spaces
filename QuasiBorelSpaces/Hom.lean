import QuasiBorelSpaces.Nat
import QuasiBorelSpaces.Prod

/-!
# Exponentials of Quasi-Borel Spaces

This file defines the exponential object in the category of quasi-borel spaces.

See [HeunenKSY17], Proposition 18.
-/

open QuasiBorelSpace

/-- The type of morphisms between `QuasiBorelSpace`s. -/
structure QuasiBorelHom (A B : Type*) [QuasiBorelSpace A] [QuasiBorelSpace B] where
  /-- The underlying function. -/
  toFun : A → B
  /-- The underlying function is a morphism. -/
  private property : IsHom toFun := by fun_prop

namespace QuasiBorelHom

variable {A B C : Type*} [QuasiBorelSpace A] [QuasiBorelSpace B] [QuasiBorelSpace C]

@[inherit_doc]
infixr:25 " →𝒒 " => QuasiBorelHom

instance : FunLike (A →𝒒 B) A B where
  coe := toFun
  coe_injective' f g := by
    cases f
    cases g
    simp only [mk.injEq, imp_self]

/-- A simps projection for function coercion. -/
def Simps.coe (f : A →𝒒 B) : A → B := f

initialize_simps_projections QuasiBorelHom (toFun → coe)

@[ext]
lemma ext {f g : A →𝒒 B} (h : ∀ x, f x = g x) : f = g := DFunLike.ext f g h

/--
Copy of a `QuasiBorelHom` with a new `toFun` equal to the old one.
Useful to fix definitional equalities.
-/
protected def copy (f : A →𝒒 B) (f' : A → B) (h : f' = ⇑f) : A →𝒒 B where
  toFun := f'
  property := h.symm ▸ f.property

@[simp]
lemma coe_mk {f : A → B} (hf : IsHom f) : ⇑(mk f hf) = f := rfl

@[simp]
lemma eta (f : A →𝒒 B) : mk f f.property = f := rfl

@[simp]
lemma toFun_eq_coe (f : A →𝒒 B) : toFun f = ⇑f := rfl

@[simp, fun_prop]
lemma isHom_coe (f : A →𝒒 B) : IsHom ⇑f := f.property

instance : QuasiBorelSpace (A →𝒒 B) where
  IsVar φ := IsHom (fun x : ℝ × A ↦ φ x.1 x.2)
  isVar_const f := by fun_prop
  isVar_comp hf hφ := by
    rw [←isHom_iff_measurable] at hf
    fun_prop
  isVar_cases' {ix} {φ} hix hφ := by
    rw [←isHom_iff_measurable] at hix
    apply isHom_cases (f := fun n (x : _ × _) ↦ (φ n x.1) x.2)
    · fun_prop
    · fun_prop

@[local simp]
lemma isHom_def (φ : ℝ → A →𝒒 B) : IsHom φ ↔ IsHom (fun x : ℝ × A ↦ φ x.1 x.2) := by
  rw [←isVar_iff_isHom]
  rfl

@[fun_prop, simp]
lemma isHom_eval : IsHom (fun p : (A →𝒒 B) × A => p.1 p.2) := by
  rw [QuasiBorelSpace.isHom_def]
  simp only [Prod.isHom_iff, isHom_def, and_imp]
  intro φ hφ₁ hφ₂
  apply @hφ₁ fun r ↦ (r, (φ r).2)
  simp only [Prod.isHom_iff, isHom_id', true_and]
  exact hφ₂

@[fun_prop]
lemma isHom_eval'
    {f : A → B →𝒒 C} (hf : IsHom f)
    {g : A → B} (hg : IsHom g)
    : IsHom (fun x ↦ f x (g x)) := by
  apply isHom_comp' (f := fun x ↦ x.1 x.2) (g := fun x ↦ (f x, g x))
  · simp only [isHom_eval]
  · fun_prop

@[simp]
lemma isHom_iff (f : A → B →𝒒 C) : IsHom f ↔ IsHom (fun x : A × B ↦ f x.1 x.2) := by
  apply Iff.intro
  · intro hf
    rw [QuasiBorelSpace.isHom_def]
    simp only [Prod.isHom_iff, and_imp]
    intro φ hφ₁ hφ₂
    fun_prop
  · intro hf
    rw [QuasiBorelSpace.isHom_def]
    intro φ hφ
    simp only [isHom_def]
    fun_prop

@[fun_prop]
lemma isHom_mk
    {f : A → B → C} (hf : IsHom (fun x : A × B ↦ f x.1 x.2))
    : IsHom (fun x ↦ mk (f x) (by fun_prop)) := by
  simp only [isHom_iff, coe_mk, hf]

/-- Currying for `QuasiBorelHom`s. -/
@[simps coe]
def curry (f : A × B →𝒒 C) : A →𝒒 B →𝒒 C where
  toFun x := { toFun y := f (x, y) }
  property := by
    simp only [isHom_iff, coe_mk, Prod.mk.eta]
    fun_prop

/-- Uncurrying for `QuasiBorelHom`s. -/
@[simps coe]
def uncurry (f : A →𝒒 B →𝒒 C) : A × B →𝒒 C where
  toFun x := f x.1 x.2

@[simp]
lemma curry_uncurry (f : A →𝒒 B →𝒒 C) : curry (uncurry f) = f := rfl

@[simp]
lemma uncurry_curry (f : A × B →𝒒 C) : uncurry (curry f) = f := rfl

end QuasiBorelHom
