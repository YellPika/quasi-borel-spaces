import QuasiBorelSpaces.Basic
import QuasiBorelSpaces.Subtype
import QuasiBorelSpaces.Sum

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
  simp only [isVar_iff_measurable] at ⊢ hf
  apply Measurable.not hf

@[fun_prop]
lemma isHom_and
    {f g : A → Prop} (hf : IsHom f) (hg : IsHom g)
    : IsHom (fun x ↦ f x ∧ g x) := by
  intro φ hφ
  specialize hf hφ
  specialize hg hφ
  simp only [isVar_iff_measurable] at ⊢ hf hg
  apply Measurable.and hf hg

@[fun_prop]
lemma isHom_or
    {f g : A → Prop} (hf : IsHom f) (hg : IsHom g)
    : IsHom (fun x ↦ f x ∨ g x) := by
  intro φ hφ
  specialize hf hφ
  specialize hg hφ
  simp only [isVar_iff_measurable] at ⊢ hf hg
  apply Measurable.or hf hg

lemma isHom_imp
    {f g : A → Prop} (hf : IsHom f) (hg : IsHom g)
    : IsHom (fun x ↦ f x → g x) := by
  intro φ hφ
  specialize hf hφ
  specialize hg hφ
  simp only [isVar_iff_measurable] at ⊢ hf hg
  apply Measurable.imp hf hg

@[fun_prop]
lemma isHom_iff
    {f g : A → Prop} (hf : IsHom f) (hg : IsHom g)
    : IsHom (fun x ↦ f x ↔ g x) := by
  intro φ hφ
  specialize hf hφ
  specialize hg hφ
  simp only [isVar_iff_measurable] at ⊢ hf hg
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
  simp only [isVar_iff_measurable] at hf
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
  simp only [isVar_iff_measurable] at hf
  exact hf

@[fun_prop]
lemma isHom_dite
    {p : A → Prop} (hp : IsHom p) [inst : DecidablePred p]
    {f : (x : A) → p x → B} (hf : IsHom fun x : Subtype p ↦ f x.val x.property)
    {g : (x : A) → ¬p x → B} (hg : IsHom fun x : Subtype (fun x ↦ ¬p x) ↦ g x.val x.property)
    : IsHom (fun x ↦ if h : p x then f x h else g x h) := by
  classical
  have : inst = fun x ↦ Classical.dec _ := by subsingleton
  subst this

  wlog hp : Nonempty (Subtype p)
  · simp only [nonempty_subtype, not_exists] at hp
    simp only [hp, ↓reduceDIte]
    have : IsHom fun x : A ↦ (⟨x, hp x⟩ : Subtype fun x ↦ ¬p x) := by fun_prop
    apply isHom_comp' hg this

  wlog hnp : Nonempty (Subtype fun x ↦ ¬p x)
  · simp only [nonempty_subtype, not_exists, Decidable.not_not] at hnp
    simp only [hnp, ↓reduceDIte]
    have : IsHom fun x : A ↦ (⟨x, hnp x⟩ : Subtype p) := by fun_prop
    apply isHom_comp' hf this

  let f' := fun x : Subtype p ↦ f x.val x.property
  let g' := fun x : Subtype (fun x ↦ ¬p x) ↦ g x.val x.property
  let k q x :=
      if q
      then f' (if h : p x then ⟨x, h⟩ else Classical.arbitrary _)
      else g' (if h : ¬p x then ⟨x, h⟩ else Classical.arbitrary _)

  have := isHom_cases (ix := fun x : A ↦ p x) (f := k)
  have {x} : (if h : p x then f x h else g x h) = k (p x) x := by
    by_cases h : p x
    · simp only [h, ↓reduceDIte, dite_not, if_true, k, f']
    · simp only [h, ↓reduceDIte, dite_not, if_false, k, g']

  simp only [this]
  unfold k
  apply isHom_ite
  · fun_prop
  · apply isHom_comp' hf
    simp only [Subtype.isHom_iff]
    have {x}
        : (if h : p x then ⟨x, h⟩ else Classical.arbitrary (Subtype p)).val
        = (if p x then x else (Classical.arbitrary (Subtype p)).val) := by
      by_cases h : p x
      · simp only [h, ↓reduceDIte, ↓reduceIte]
      · simp only [h, ↓reduceDIte, ↓reduceIte]
    simp only [this]
    apply isHom_ite
    · fun_prop
    · fun_prop
    · fun_prop
  · apply isHom_comp' hg
    simp only [Subtype.isHom_iff]
    have {x}
        : (if h : ¬p x then ⟨x, h⟩ else Classical.arbitrary (Subtype fun x ↦ ¬p x)).val
        = (if ¬p x then x else (Classical.arbitrary (Subtype fun x ↦ ¬p x)).val) := by
      by_cases h : p x
      · simp only [h, not_true_eq_false, ↓reduceDIte, ↓reduceIte]
      · simp only [h, not_false_eq_true, ↓reduceDIte, ↓reduceIte]
    simp only [this]
    apply isHom_ite
    · fun_prop
    · fun_prop
    · fun_prop

end QuasiBorelSpace.Prop
