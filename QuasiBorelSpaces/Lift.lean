import QuasiBorelSpaces.Basic

variable {A B : Type*} [QuasiBorelSpace A] [QuasiBorelSpace B]

namespace QuasiBorelSpace.ULift

instance : QuasiBorelSpace (ULift A) := lift ULift.down

@[simp]
lemma var_iff {φ : ℝ → ULift A} : IsVar φ ↔ IsVar (fun x ↦ (φ x).down) := by rfl

@[simp]
lemma isHom_iff {φ : A → ULift B} : IsHom φ ↔ IsHom (fun x ↦ (φ x).down) := by rfl

@[fun_prop]
lemma isHom_up {f : A → B} (hf : IsHom f) : IsHom (fun x ↦ ULift.up (f x)) := by
  simp only [isHom_iff, hf]

@[fun_prop]
lemma isHom_down {f : A → ULift B} (hf : IsHom f) : IsHom (fun x ↦ ULift.down (f x)) := by
  simp only [isHom_iff] at hf
  exact hf

end QuasiBorelSpace.ULift

namespace QuasiBorelSpace.PLift

instance : QuasiBorelSpace (PLift A) := lift PLift.down

@[simp]
lemma var_iff {φ : ℝ → PLift A} : IsVar φ ↔ IsVar (fun x ↦ (φ x).down) := by rfl

@[simp]
lemma isHom_iff {φ : A → PLift B} : IsHom φ ↔ IsHom (fun x ↦ (φ x).down) := by rfl

@[fun_prop]
lemma isHom_up {f : A → B} (hf : IsHom f) : IsHom (fun x ↦ PLift.up (f x)) := by
  simp only [isHom_iff, hf]

@[fun_prop]
lemma isHom_down {f : A → PLift B} (hf : IsHom f) : IsHom (fun x ↦ PLift.down (f x)) := by
  simp only [isHom_iff] at hf
  exact hf

end QuasiBorelSpace.PLift
