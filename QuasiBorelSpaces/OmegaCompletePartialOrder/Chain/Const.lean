import Mathlib.Order.OmegaCompletePartialOrder

namespace OmegaCompletePartialOrder.Chain

variable {A : Type*} [Preorder A]

/-- The chain that always returns the same value. -/
def const (x : A) : Chain A := OrderHom.const ℕ x

@[simp]
lemma const_apply (x : A) (n : ℕ) : const x n = x := rfl

end OmegaCompletePartialOrder.Chain
