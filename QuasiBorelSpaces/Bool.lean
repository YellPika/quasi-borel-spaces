import QuasiBorelSpaces.Basic

namespace QuasiBorelSpace.Bool

@[simps!]
instance : QuasiBorelSpace Bool := ofMeasurableSpace

example : DiscreteQuasiBorelSpace Bool := inferInstance

end QuasiBorelSpace.Bool
