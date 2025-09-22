import QuasiBorelSpaces.Prod

namespace QuasiBorelSpace.Pi

variable
  {A : Type*} [QuasiBorelSpace A]
  {B : Type*} [QuasiBorelSpace B]
  {C : Type*} [QuasiBorelSpace C]
  {I : Type*} {P : I → Type*} [∀ i, QuasiBorelSpace (P i)]

instance : QuasiBorelSpace (∀i : I, P i) where
  IsVar φ := ∀ i, IsHom (φ · i)
  isVar_const f i := by simp only [isHom_const]
  isVar_comp hf hφ i := by
    rw [←isHom_iff_measurable] at hf
    fun_prop
  isVar_cases' hix hφ i :=
    isHom_cases (by simp only [isHom_ofMeasurableSpace, hix]) (hφ · i)

@[local simp]
lemma isHom_def (φ : ℝ → ∀ i, P i) : IsHom φ ↔ ∀ i, IsHom (φ · i) := by
  rw [←isVar_iff_isHom]
  rfl

@[fun_prop]
lemma isHom_apply (i : I) : IsHom (fun (f : (i : I) → P i) ↦ f i) := by
  rw [QuasiBorelSpace.isHom_def]
  simp only [isHom_def]
  fun_prop

@[fun_prop]
lemma isHom_pi {f : A → ∀ i, P i} (hf : ∀ i, IsHom (f · i)) : IsHom f := by
  rw [QuasiBorelSpace.isHom_def]
  simp only [isHom_def]
  fun_prop

@[simp]
lemma isHom_iff {f : A → (i : I) → P i} : IsHom f ↔ ∀i, IsHom (f · i) := by
  apply Iff.intro
  · fun_prop
  · exact isHom_pi

instance
    [∀ i, MeasurableSpace (P i)]
    [∀ i, MeasurableQuasiBorelSpace (P i)]
    : MeasurableQuasiBorelSpace (∀i, P i) where
  isHom_iff_measurable φ := by
    apply Iff.intro <;>
    · simp only [isHom_iff, isHom_iff_measurable]
      fun_prop

end QuasiBorelSpace.Pi
