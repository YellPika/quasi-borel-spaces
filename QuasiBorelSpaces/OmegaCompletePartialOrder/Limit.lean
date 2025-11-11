import Mathlib.Order.OmegaCompletePartialOrder

/-!
# Limits and pointwise ω-suprema for ωCPOs

This file defines:
- Basic omega-limit operations
- Pointwise ω-suprema for function spaces needed in the compatibility axiom for ωQBS
-/

namespace QuasiBorelSpaces.OmegaCompletePartialOrder
open _root_.OmegaCompletePartialOrder

universe u v

/-- abbreviation for omega chain -/
abbrev Chain (α : Type u) [_root_.OmegaCompletePartialOrder α] :=
  _root_.OmegaCompletePartialOrder.Chain α

variable {α : Type u} [_root_.OmegaCompletePartialOrder α]

/-- the omega-limit of a chain is its omega-supremum -/
def omegaLimit {α : Type u} [OmegaCompletePartialOrder α] (c : Chain α) : α := ωSup c

/-- the omega-limit is a least upper bound -/
lemma omegaLimit_isLUB (c : Chain α) :
  IsLUB (Set.range c) (omegaLimit c) :=
  isLUB_range_ωSup c

/-- the omega-limit is unique -/
lemma omegaLimit_unique (c : Chain α) {l : α}
  (hl : IsLUB (Set.range c) l) : l = omegaLimit c :=
  ωSup_eq_of_isLUB hl

section FunctionSpace

variable {ι : Type u} {α : Type v} [OmegaCompletePartialOrder α]

/-- evaluation at a point as an order homomorphism -/
def evalOrderHom (x : ι) : (ι → α) →o α where
  toFun f := f x
  monotone' _f _g h := h x

@[simp]
lemma evalOrderHom_apply (x : ι) (f : ι → α) : evalOrderHom x f = f x := rfl

/--
pointwise omega-supremum: the omega-supremum of a chain of functions
is the function that takes omega-supremum pointwise
-/
lemma ωSup_eval (c : Chain (ι → α)) (x : ι) :
    (ωSup c) x = ωSup (c.map (evalOrderHom x)) := by
  apply le_antisymm
  · apply ωSup_le
    intro n
    have : c n x ≤ ωSup (c.map (evalOrderHom x)) := by
      apply le_ωSup (c.map (evalOrderHom x)) n
    exact this
  · apply ωSup_le
    intro n
    have : ωSup c x ≥ c n x := by
      have := le_ωSup c n
      exact this x
    exact this

end FunctionSpace

end QuasiBorelSpaces.OmegaCompletePartialOrder
