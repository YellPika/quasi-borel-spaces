import QuasiBorelSpaces.Basic

variable
  {A B : Type*} [QuasiBorelSpace A] [QuasiBorelSpace B]
  {I : Type*} [Countable I]

namespace QuasiBorelSpace.Prop

@[simps!]
instance : QuasiBorelSpace Prop := ofMeasurableSpace

example : DiscreteQuasiBorelSpace Prop := inferInstance

@[fun_prop]
lemma isHom_ite
    {p : A → Prop} (hp : IsHom p) [inst : DecidablePred p]
    {f : A → B} (hf : IsHom f)
    {g : A → B} (hg : IsHom g)
    : IsHom (fun x ↦ if p x then f x else g x) := by
  classical
  have (x : A) : inst x = Classical.dec _ := by subsingleton
  conv => enter [1, x]; rw [this]
  apply isHom_cases (f := fun b x ↦ if b then f x else g x) hp
  intro q
  by_cases hq : q
  · simp only [hq, ↓reduceIte, hf]
  · simp only [hq, ↓reduceIte, hg]

@[fun_prop]
lemma isHom_not
    {f : A → Prop} (hf : IsHom f)
    : IsHom (fun x ↦ ¬f x) := by
  intro φ hφ
  specialize hf hφ
  simp only [DiscreteQuasiBorelSpace.isVar_iff_measurable] at ⊢ hf
  apply Measurable.not hf

@[fun_prop]
lemma isHom_and
    {f g : A → Prop} (hf : IsHom f) (hg : IsHom g)
    : IsHom (fun x ↦ f x ∧ g x) := by
  intro φ hφ
  specialize hf hφ
  specialize hg hφ
  simp only [DiscreteQuasiBorelSpace.isVar_iff_measurable] at ⊢ hf hg
  apply Measurable.and hf hg

@[fun_prop]
lemma isHom_or
    {f g : A → Prop} (hf : IsHom f) (hg : IsHom g)
    : IsHom (fun x ↦ f x ∨ g x) := by
  intro φ hφ
  specialize hf hφ
  specialize hg hφ
  simp only [DiscreteQuasiBorelSpace.isVar_iff_measurable] at ⊢ hf hg
  apply Measurable.or hf hg

lemma isHom_imp
    {f g : A → Prop} (hf : IsHom f) (hg : IsHom g)
    : IsHom (fun x ↦ f x → g x) := by
  intro φ hφ
  specialize hf hφ
  specialize hg hφ
  simp only [DiscreteQuasiBorelSpace.isVar_iff_measurable] at ⊢ hf hg
  apply Measurable.imp hf hg

@[fun_prop]
lemma isHom_iff
    {f g : A → Prop} (hf : IsHom f) (hg : IsHom g)
    : IsHom (fun x ↦ f x ↔ g x) := by
  intro φ hφ
  specialize hf hφ
  specialize hg hφ
  simp only [DiscreteQuasiBorelSpace.isVar_iff_measurable] at ⊢ hf hg
  apply Measurable.iff hf hg

lemma isHom_forall
    [QuasiBorelSpace I]
    {f : I → A → Prop} (hf : ∀ i, IsHom (f i))
    : IsHom (fun x ↦ ∀i, f i x) := by
  intro φ hφ
  dsimp only [default_IsVar]
  apply Measurable.forall
  intro i
  specialize hf i hφ
  simp only [DiscreteQuasiBorelSpace.isVar_iff_measurable] at hf
  exact hf

@[fun_prop]
lemma isHom_exists
    [QuasiBorelSpace I]
    {f : I → A → Prop} (hf : ∀ i, IsHom (f i))
    : IsHom (fun x ↦ ∃i, f i x) := by
  intro φ hφ
  dsimp only [default_IsVar]
  apply Measurable.exists
  intro i
  specialize hf i hφ
  simp only [DiscreteQuasiBorelSpace.isVar_iff_measurable] at hf
  exact hf

end QuasiBorelSpace.Prop
