import QuasiBorelSpaces.Basic

namespace QuasiBorelSpace.Quotient

variable {A B : Type*} [QuasiBorelSpace A] [QuasiBorelSpace B] {S : Setoid A}

@[simps]
instance : QuasiBorelSpace (Quotient S) where
  IsVar φ := ∃(ψ : ℝ → A), IsVar ψ ∧ ∀r, φ r = ⟦ψ r⟧
  isVar_const x := by
    induction x using Quotient.inductionOn with | h x =>
    use fun _ ↦ x
    simp only [isVar_const, implies_true, and_self]
  isVar_comp {f} {φ} hf hφ := by
    rcases hφ with ⟨ψ, hψ, hφ⟩
    use fun x ↦ ψ (f x)
    apply And.intro
    · apply isVar_comp hf hψ
    · simp only [hφ, implies_true]
  isVar_cases' {index} {φ} hindex hφ := by
    choose ψ hψ hφ using hφ
    use fun r ↦ ψ (index r) r
    apply And.intro
    · apply isVar_cases' hindex hψ
    · simp only [hφ, implies_true]

@[simp, fun_prop]
lemma isHom_mk : IsHom (fun x ↦ (⟦x⟧ : Quotient S)) := by
  intro φ hφ
  simp only [IsVar_def, Quotient.eq]
  use φ
  simp only [hφ, true_and]
  intro r
  rfl

@[simp, fun_prop]
lemma isHom_lift
    {f : A → B} (hf₁ : IsHom f) (hf₂ : ∀ x y, x ≈ y → f x = f y)
    : IsHom (Quotient.lift f hf₂ : Quotient S → B) := by
  intro φ hφ
  simp only [IsVar_def] at ⊢ hφ
  rcases hφ with ⟨ψ, hψ, hφ⟩
  simp only [hφ, Quotient.lift_mk]
  apply hf₁
  apply hψ

end QuasiBorelSpace.Quotient
