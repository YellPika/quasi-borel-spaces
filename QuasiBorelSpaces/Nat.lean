import QuasiBorelSpaces.Basic

namespace QuasiBorelSpace.Nat

@[simps!]
instance : QuasiBorelSpace ℕ := ofMeasurableSpace

example : DiscreteQuasiBorelSpace ℕ := inferInstance

end QuasiBorelSpace.Nat
