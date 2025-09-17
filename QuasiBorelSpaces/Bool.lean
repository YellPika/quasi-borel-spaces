import QuasiBorelSpaces.Prop

namespace QuasiBorelSpace.Bool

variable {A : Type*} [QuasiBorelSpace A]

@[simps!]
instance : QuasiBorelSpace Bool := ofMeasurableSpace

example : DiscreteQuasiBorelSpace Bool := inferInstance

@[fun_prop]
lemma isHom_decide
    {p : A → Prop} [inst : DecidablePred p] (hp : IsHom p)
    : IsHom (fun x ↦ decide (p x)) := by
  classical
  have : inst = fun x ↦ Classical.dec (p x) := by subsingleton
  subst this
  apply isHom_cases (f := fun p _ ↦ decide p) <;> fun_prop

end QuasiBorelSpace.Bool
