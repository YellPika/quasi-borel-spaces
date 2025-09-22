import QuasiBorelSpaces.Basic

namespace QuasiBorelSpace.Quotient

variable {A B : Type*} [QuasiBorelSpace A] [QuasiBorelSpace B] {S : Setoid A}

@[simps]
instance : QuasiBorelSpace (Quotient S) where
  IsVar φ := ∃(ψ : ℝ → A), IsHom ψ ∧ ∀r, φ r = ⟦ψ r⟧
  isVar_const x := by
    induction x using Quotient.inductionOn with | h x =>
    use fun _ ↦ x
    simp only [isHom_const, implies_true, and_self]
  isVar_comp {f} {φ} hf hφ := by
    rcases hφ with ⟨ψ, hψ, hφ⟩
    use fun x ↦ ψ (f x)
    apply And.intro
    · fun_prop
    · simp only [hφ, implies_true]
  isVar_cases' {index} {φ} hindex hφ := by
    choose ψ hψ hφ using hφ
    use fun r ↦ ψ (index r) r
    apply And.intro
    · apply isHom_cases (by simp only [isHom_ofMeasurableSpace, hindex]) hψ
    · simp only [hφ, implies_true]

@[simp]
lemma isHom_def (φ : ℝ → Quotient S) : IsHom φ ↔ ∃(ψ : ℝ → A), IsHom ψ ∧ ∀r, φ r = ⟦ψ r⟧ := by
  rw [← isVar_iff_isHom]
  rfl

@[simp, fun_prop]
lemma isHom_mk : IsHom (fun x ↦ (⟦x⟧ : Quotient S)) := by
  rw [QuasiBorelSpace.isHom_def]
  simp only [isHom_def, Quotient.eq]
  intro φ hφ
  use φ
  simp only [hφ, true_and]
  intro r
  rfl

@[simp, fun_prop]
lemma isHom_lift
    {f : A → B} (hf₁ : IsHom f) (hf₂ : ∀ x y, x ≈ y → f x = f y)
    : IsHom (Quotient.lift f hf₂ : Quotient S → B) := by
  rw [QuasiBorelSpace.isHom_def]
  simp only [isHom_def, forall_exists_index, and_imp]
  intro φ ψ hψ hφ
  simp only [hφ, Quotient.lift_mk]
  fun_prop

end QuasiBorelSpace.Quotient
