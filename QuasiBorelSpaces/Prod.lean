import QuasiBorelSpaces.Basic
import QuasiBorelSpaces.OmegaQuasiBorelSpace
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Binary Products of Quasi-Borel Spaces

This file defines binary products of quasi-borel spaces by giving a
`QuasiBorelSpace` instance for the `· × ·` type.

See [HeunenKSY17], Proposition 16.
-/

namespace QuasiBorelSpace.Prod

variable
  {A : Type*} [QuasiBorelSpace A]
  {B : Type*} [QuasiBorelSpace B]
  {C : Type*} [QuasiBorelSpace C]
  {D : Type*} [QuasiBorelSpace D]

instance : QuasiBorelSpace (A × B) where
  IsVar φ := IsHom (fun x ↦ Prod.fst (φ x)) ∧ IsHom (fun x ↦ Prod.snd (φ x))
  isVar_const x := by
    simp only [isHom_const, and_self]
  isVar_comp hf := by
    rintro ⟨hφ₁, hφ₂⟩
    apply And.intro
    · apply isHom_comp' hφ₁
      simp only [isHom_ofMeasurableSpace, hf]
    · apply isHom_comp' hφ₂
      simp only [isHom_ofMeasurableSpace, hf]
  isVar_cases' {ix} {φ} hix hφ := by
    apply And.intro
    · apply isHom_cases (ix := ix) (f := fun n r ↦ (φ n r).1) ?_ (fun n ↦ (hφ n).1)
      simp only [isHom_ofMeasurableSpace, hix]
    · apply isHom_cases (ix := ix) (f := fun n r ↦ (φ n r).2) ?_ (fun n ↦ (hφ n).2)
      simp only [isHom_ofMeasurableSpace, hix]

@[local simp]
lemma isHom_def (f : ℝ → A × B) : IsHom f ↔ IsHom (fun x ↦ (f x).1) ∧ IsHom (fun x ↦ (f x).2) := by
  rw [← isVar_iff_isHom]
  rfl

@[simp]
lemma isHom_fst : IsHom (Prod.fst : A × B → A) := by
  rw [QuasiBorelSpace.isHom_def]
  simp_all only [isHom_def, implies_true]

@[fun_prop]
lemma isHom_fst' {f : A → B × C} (hf : IsHom f) : IsHom (fun x ↦ (f x).1) :=
  isHom_comp isHom_fst hf

@[simp]
lemma isHom_snd : IsHom (Prod.snd : A × B → B) := by
  rw [QuasiBorelSpace.isHom_def]
  simp_all only [isHom_def, implies_true]

@[fun_prop]
lemma isHom_snd' {f : A → B × C} (hf : IsHom f) : IsHom (fun x ↦ (f x).2) :=
  isHom_comp isHom_snd hf

@[fun_prop]
lemma isHom_mk
    {f : A → B} (hf : IsHom f)
    {g : A → C} (hg : IsHom g)
    : IsHom (fun x ↦ (f x, g x)) := by
  rw [QuasiBorelSpace.isHom_def] at ⊢ hf hg
  simp only [isHom_def]
  grind

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
  isHom_iff_measurable φ := by
    simp only [isHom_iff, isHom_iff_measurable]
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

variable {α β : Type*} [QuasiBorelSpace α] [QuasiBorelSpace β]

lemma isHom_fst_comp {f : ℝ → α × β} (hf : IsHom f) :
    IsHom (fun r => (f r).1) :=
  (isHom_iff f).mp hf |>.1

lemma isHom_snd_comp {f : ℝ → α × β} (hf : IsHom f) :
    IsHom (fun r => (f r).2) :=
  (isHom_iff f).mp hf |>.2

end QuasiBorelSpace.Prod

namespace OmegaQuasiBorelSpace.Prod

open QuasiBorelSpace
open OmegaCompletePartialOrder

variable {A B : Type*} [OmegaQuasiBorelSpace A] [OmegaQuasiBorelSpace B]

instance : OmegaQuasiBorelSpace (A × B) where
  isHom_ωSup' c hc := by
    rw [Prod.isHom_iff]
    constructor
    · let c₁ := c.map ⟨(fun f r ↦ (f r).1), by intro f g h r; exact (h r).1⟩
      apply isHom_ωSup c₁ fun n ↦ ?_
      simp only [Chain.map_coe, OrderHom.coe_mk, Function.comp_apply, c₁]
      fun_prop
    · let c₂ := c.map ⟨(fun f r ↦ (f r).2), by intro f g h r; exact (h r).2⟩
      apply isHom_ωSup c₂ fun n ↦ ?_
      simp only [Chain.map_coe, OrderHom.coe_mk, Function.comp_apply, c₂]
      fun_prop

end OmegaQuasiBorelSpace.Prod

namespace QuasiBorelSpace

variable {A B : Type*} [QuasiBorelSpace A] [QuasiBorelSpace B]

-- TODO: move this to a more appropriate file
@[fun_prop]
lemma Measure.isHom_lintegral
    [MeasurableSpace A] [MeasurableSpace B] [StandardBorelSpace B] [MeasurableQuasiBorelSpace B]
    {f : A → B → ENNReal} (hf : IsHom fun x : _ × _ ↦ f x.1 x.2)
    (μ : MeasureTheory.Measure B) [MeasureTheory.SFinite μ]
    : IsHom fun x ↦ ∫⁻ y, f x y ∂μ := by
  rw [isHom_def]
  intro φ hφ
  apply isHom_of_measurable
  apply Measurable.lintegral_prod_left
  apply measurable_of_isHom
  fun_prop

end QuasiBorelSpace
