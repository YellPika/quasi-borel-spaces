import QuasiBorelSpaces.Basic
import QuasiBorelSpaces.Nat
import QuasiBorelSpaces.MeasureTheory.Pack

namespace QuasiBorelSpace.Prod

variable
  {A : Type*} [QuasiBorelSpace A]
  {B : Type*} [QuasiBorelSpace B]
  {C : Type*} [QuasiBorelSpace C]
  {D : Type*} [QuasiBorelSpace D]

@[simps IsVar]
instance : QuasiBorelSpace (A × B) where
  IsVar φ := IsVar (fun x ↦ Prod.fst (φ x)) ∧ IsVar (fun x ↦ Prod.snd (φ x))
  isVar_const x := by
    apply And.intro
    · apply isVar_const x.1
    · apply isVar_const x.2
  isVar_comp f hf := by
    apply And.intro
    · apply isVar_comp f hf.1
    · apply isVar_comp f hf.2
  isVar_cases' {ix} {φ} hix hφ := by
    apply And.intro
    · apply isVar_cases' (ix := ix) (φ := fun n r ↦ (φ n r).1) hix (fun n ↦ (hφ n).1)
    · apply isVar_cases' (ix := ix) (φ := fun n r ↦ (φ n r).2) hix (fun n ↦ (hφ n).2)

@[simp]
lemma isHom_fst : IsHom (Prod.fst : A × B → A) := by
  intro φ ⟨hφ₁, hφ₂⟩
  apply hφ₁

@[fun_prop]
lemma isHom_fst' {f : A → B × C} (hf : IsHom f) : IsHom (fun x ↦ (f x).1) :=
  isHom_comp isHom_fst hf

@[simp]
lemma isHom_snd : IsHom (Prod.snd : A × B → B) := by
  intro φ ⟨hφ₁, hφ₂⟩
  apply hφ₂

@[fun_prop]
lemma isHom_snd' {f : A → B × C} (hf : IsHom f) : IsHom (fun x ↦ (f x).2) :=
  isHom_comp isHom_snd hf

@[fun_prop]
lemma isHom_mk
    {f : A → B} (hf : IsHom f)
    {g : A → C} (hg : IsHom g)
    : IsHom (fun x ↦ (f x, g x)) := by
  intro φ hφ
  refine ⟨?_, ?_⟩
  · apply hf hφ
  · apply hg hφ

@[simp]
lemma isHom_iff (f : A → B × C) : IsHom f ↔ IsHom (fun x ↦ (f x).1) ∧ IsHom (fun x ↦ (f x).2) := by
  apply Iff.intro
  · intro hf
    exact ⟨isHom_fst' hf, isHom_snd' hf⟩
  · rintro ⟨h₁, h₂⟩
    exact isHom_mk h₁ h₂

instance
    [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableQuasiBorelSpace A] [MeasurableQuasiBorelSpace B]
    : MeasurableQuasiBorelSpace (A × B) where
  isVar_iff_measurable φ := by
    simp only [IsVar_def, isVar_iff_measurable]
    apply Iff.intro
    · rintro ⟨h₁, h₂⟩
      apply Measurable.prodMk h₁ h₂
    · intro h
      apply And.intro
      · fun_prop
      · fun_prop

@[fun_prop]
lemma isHom_map {f : A → B} {g : C → D} (hf : IsHom f) (hg : IsHom g) : IsHom (Prod.map f g) := by
  simp only [isHom_iff, Prod.map_fst, Prod.map_snd]
  apply And.intro <;> fun_prop

lemma isHom_of_uncurry
    {f : A → B → C} (hf : IsHom (Function.uncurry f))
    {g : D → A} (hg : IsHom g)
    {h : D → B} (hh : IsHom h)
    : IsHom fun x ↦ f (g x) (h x) := by
  apply isHom_comp' (f := Function.uncurry f) (g := fun x ↦ (g x, h x))
  · apply hf
  · fun_prop

end QuasiBorelSpace.Prod
