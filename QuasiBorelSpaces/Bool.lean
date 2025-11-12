import QuasiBorelSpaces.Basic

namespace QuasiBorelSpace.Bool

variable {A : Type*} [QuasiBorelSpace A]

@[simps!]
instance : QuasiBorelSpace Bool := ofMeasurableSpace

example : DiscreteQuasiBorelSpace Bool := inferInstance

end QuasiBorelSpace.Bool
