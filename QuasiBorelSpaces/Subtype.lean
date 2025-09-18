import QuasiBorelSpaces.Basic

namespace QuasiBorelSpace.Subtype

variable {A B : Type*} [QuasiBorelSpace A] [QuasiBorelSpace B] {P : A → Prop}

@[simps!]
instance : QuasiBorelSpace (Subtype P) := lift Subtype.val

instance
    [MeasurableSpace A] [MeasurableQuasiBorelSpace A]
    : MeasurableQuasiBorelSpace (Subtype P) where
  isVar_iff_measurable φ := by
    apply Iff.intro
    · intro h
      simp only [IsVar_def, isVar_iff_measurable] at h
      exact h.subtype_mk
    · intro h
      simp only [IsVar_def, isVar_iff_measurable]
      apply h.subtype_val

@[simp]
lemma isHom_iff {P : B → Prop} (f : A → Subtype P) : IsHom f ↔ IsHom fun x ↦ (f x).val := by
  apply Iff.intro
  · intro hf φ hφ
    apply hf
    apply hφ
  · intro hf φ hφ
    apply hf
    apply hφ

@[fun_prop]
lemma isHom_mk {P : B → Prop}
    {f : A → B} (hf₁ : IsHom f) (hf₂ : (x : A) → P (f x))
    : IsHom (fun x ↦ Subtype.mk (f x) (hf₂ x)) := by
  simp only [isHom_iff]
  apply hf₁

@[fun_prop]
lemma isHom_val {P : B → Prop} {f : A → Subtype P} (hf : IsHom f) : IsHom (fun x ↦ (f x).val) := by
  rw [←isHom_iff]
  exact hf

end QuasiBorelSpace.Subtype
