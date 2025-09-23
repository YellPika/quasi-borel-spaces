import QuasiBorelSpaces.Basic
import QuasiBorelSpaces.Pi
import QuasiBorelSpaces.Subtype
import QuasiBorelSpaces.Sum

variable
  {A B : Type*} [QuasiBorelSpace A] [QuasiBorelSpace B]
  {I : Type*} [Countable I]

namespace QuasiBorelSpace.Prop

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
  fun_prop

@[fun_prop]
lemma isHom_and
    {f g : A → Prop} (hf : IsHom f) (hg : IsHom g)
    : IsHom (fun x ↦ f x ∧ g x) := by
  fun_prop

@[fun_prop]
lemma isHom_or
    {f g : A → Prop} (hf : IsHom f) (hg : IsHom g)
    : IsHom (fun x ↦ f x ∨ g x) := by
  fun_prop

lemma isHom_imp
    {f g : A → Prop} (hf : IsHom f) (hg : IsHom g)
    : IsHom (fun x ↦ f x → g x) := by
  apply isHom_comp' (f := fun x ↦ x.1 → x.2) (g := fun x ↦ (f x, g x))
  · simp only [isHom_of_discrete_countable]
  · fun_prop

@[fun_prop]
lemma isHom_iff
    {f g : A → Prop} (hf : IsHom f) (hg : IsHom g)
    : IsHom (fun x ↦ f x ↔ g x) := by
  fun_prop

lemma isHom_forall
    [QuasiBorelSpace I]
    {f : I → A → Prop} (hf : ∀ i, IsHom (f i))
    : IsHom (fun x ↦ ∀i, f i x) := by
  rw [isHom_def]
  intro φ hφ
  simp only [isHom_ofMeasurableSpace]
  apply Measurable.forall
  intro i
  rw [←isHom_iff_measurable]
  fun_prop

@[fun_prop]
lemma isHom_exists
    [QuasiBorelSpace I]
    {f : I → A → Prop} (hf : ∀ i, IsHom (f i))
    : IsHom (fun x ↦ ∃i, f i x) := by
  rw [isHom_def]
  intro φ hφ
  simp only [isHom_ofMeasurableSpace]
  apply Measurable.exists
  intro i
  rw [←isHom_iff_measurable]
  fun_prop

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
    simp only [Subtype.isHom_def, apply_dite, dite_eq_ite]
    apply isHom_ite
    · fun_prop
    · fun_prop
    · fun_prop
  · apply isHom_comp' hg
    simp only [Subtype.isHom_def, apply_dite, dite_eq_ite]
    apply isHom_ite
    · fun_prop
    · fun_prop
    · fun_prop

end QuasiBorelSpace.Prop
