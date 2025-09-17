import QuasiBorelSpaces.Basic

variable {A : Type*} [QuasiBorelSpace A]

namespace QuasiBorelSpace.Empty

@[simps! IsVar]
instance : QuasiBorelSpace Empty := default

example : DiscreteQuasiBorelSpace Empty := inferInstance
example (f : Empty → A) : IsHom f := by simp only [isHom_of_discrete_countable]
example (f : A → Empty) : IsHom f := by simp only [isHom_to_subsingleton]

end QuasiBorelSpace.Empty

namespace QuasiBorelSpace.PEmpty

@[simps! IsVar]
instance : QuasiBorelSpace PEmpty := default

example : DiscreteQuasiBorelSpace PEmpty := inferInstance
example (f : PEmpty → A) : IsHom f := by simp only [isHom_of_discrete_countable]
example (f : A → PEmpty) : IsHom f := by simp only [isHom_to_subsingleton]

end QuasiBorelSpace.PEmpty
