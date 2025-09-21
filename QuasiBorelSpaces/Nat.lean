import QuasiBorelSpaces.Prod

namespace QuasiBorelSpace.Nat

@[simps!]
instance : QuasiBorelSpace ℕ := ofMeasurableSpace

example : DiscreteQuasiBorelSpace ℕ := inferInstance

variable
  {A : Type*} [QuasiBorelSpace A]
  {B : Type*} [QuasiBorelSpace B]
  {C : Type*} [QuasiBorelSpace C]

@[fun_prop]
lemma isHom_rec
    {f : A → B} (hf : IsHom f)
    {g : A → ℕ → B → B} (hg : IsHom fun (x, y, z) ↦ g x y z)
    {h : A → ℕ} (hh : IsHom h)
    : IsHom (fun x ↦ (Nat.rec (f x) (g x) (h x) : B)) := by
  apply isHom_cases (ix := h) (f := fun n x ↦ (Nat.rec (f x) (g x) n : B))
  · exact hh
  · intro n
    induction n with
    | zero =>
      simp only [Nat.rec_zero]
      fun_prop
    | succ n ih =>
      simp only
      fun_prop

end QuasiBorelSpace.Nat
