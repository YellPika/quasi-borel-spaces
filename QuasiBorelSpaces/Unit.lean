import QuasiBorelSpaces.Basic

variable {A : Type*} [QuasiBorelSpace A]

namespace QuasiBorelSpace.Unit

instance : QuasiBorelSpace Unit := default

example : DiscreteQuasiBorelSpace Unit := inferInstance
example (f : Unit → A) : IsHom f := by simp only [isHom_of_discrete_countable]
example (f : A → Unit) : IsHom f := by simp only [isHom_to_subsingleton]

end QuasiBorelSpace.Unit

namespace QuasiBorelSpace.PUnit

instance : QuasiBorelSpace PUnit := default

example : DiscreteQuasiBorelSpace PUnit := inferInstance
example (f : PUnit → A) : IsHom f := by simp only [isHom_of_discrete_countable]
example (f : A → PUnit) : IsHom f := by simp only [isHom_to_subsingleton]

end QuasiBorelSpace.PUnit
