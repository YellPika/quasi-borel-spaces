import Mathlib.Order.OmegaCompletePartialOrder

namespace QuasiBorelSpaces.OmegaCompletePartialOrder
open _root_.OmegaCompletePartialOrder

universe u

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

end QuasiBorelSpaces.OmegaCompletePartialOrder
