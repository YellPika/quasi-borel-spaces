import Mathlib.Order.OmegaCompletePartialOrder
import QuasiBorelSpaces.Prod
import QuasiBorelSpaces.Sum
import QuasiBorelSpaces.OmegaCPO.Sum

/-!
# Omega quasi-borel spaces (ωQBS)

An ωQBS is a type with both an ωCPO and a QBS (Definition 3.5). This file provides the
class definition and instances for products and coproducts (Lemma 3.9).

See [VakarKS19].

## Definitions

* `OmegaQBS`: A type with both an `OmegaCompletePartialOrder` and a `QuasiBorelSpace`

## Instances
* `instOmegaQBSProd`: Products of ωQBSes form an ωQBS (Lemma 3.9)
* `instOmegaQBSSum`: Coproducts of ωQBSes form an ωQBS (Lemma 3.9)
-/

namespace QuasiBorelSpaces

universe u v

/-- an ωQBS is a type with both an `OmegaCompletePartialOrder` and a `QuasiBorelSpace`. -/
class OmegaQBS (α : Type u)
  extends OmegaCompletePartialOrder α, QuasiBorelSpace α

namespace OmegaQBS

variable {α : Type u} {β : Type v}

/-- product of ωQBSes is an ωQBS. -/
@[simp] instance instOmegaQBSProd
    [OmegaCompletePartialOrder α] [QuasiBorelSpace α]
    [OmegaCompletePartialOrder β] [QuasiBorelSpace β] : OmegaQBS (α × β) where
  toOmegaCompletePartialOrder := inferInstance
  toQuasiBorelSpace := inferInstance

/-- coproduct of ωQBSes is an ωQBS. -/
@[simp] noncomputable instance instOmegaQBSSum
    [OmegaCompletePartialOrder α] [QuasiBorelSpace α]
    [OmegaCompletePartialOrder β] [QuasiBorelSpace β] : OmegaQBS (Sum α β) where
  toOmegaCompletePartialOrder := inferInstance
  toQuasiBorelSpace := inferInstance

end OmegaQBS

end QuasiBorelSpaces
