import QuasiBorelSpaces.Prod

namespace QuasiBorelSpace.Pi

variable
  {A : Type*} [QuasiBorelSpace A]
  {B : Type*} [QuasiBorelSpace B]
  {C : Type*} [QuasiBorelSpace C]
  {I : Type*} {P : I → Type*} [∀ i, QuasiBorelSpace (P i)]

@[simps IsVar]
instance : QuasiBorelSpace (∀i : I, P i) where
  IsVar φ := ∀ i, IsVar (φ · i)
  isVar_const f i := by apply isVar_const
  isVar_comp hf hφ i := isVar_comp hf (hφ i)
  isVar_cases' hix hφ i := isVar_cases' hix (hφ · i)

@[fun_prop]
lemma isHom_apply (i : I) : IsHom (fun (f : (i : I) → P i) ↦ f i) := by
  intro φ hφ
  apply hφ

@[fun_prop]
lemma isHom_pi {f : A → ∀ i, P i} (hf : ∀ i, IsHom (f · i)) : IsHom f := by
  intro φ hφ
  apply (hf · hφ)

@[simp]
lemma isHom_iff {f : A → (i : I) → P i} : IsHom f ↔ ∀i, IsHom (f · i) := by
  apply Iff.intro
  · intro hf i
    exact isHom_comp (isHom_apply i) hf
  · exact isHom_pi

instance
    [∀ i, MeasurableSpace (P i)]
    [∀ i, MeasurableQuasiBorelSpace (P i)]
    : MeasurableQuasiBorelSpace (∀i, P i) where
  isVar_iff_measurable φ := by
    apply Iff.intro
    · intro hφ
      simp only [IsVar_def, isVar_iff_measurable] at hφ
      fun_prop
    · intro hφ i
      simp only [isVar_iff_measurable]
      fun_prop

end QuasiBorelSpace.Pi
