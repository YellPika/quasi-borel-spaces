import Mathlib.Order.OmegaCompletePartialOrder

namespace QuasiBorelSpaces.OmegaCPO
open OmegaCompletePartialOrder

universe u
variable {α : Type u} [OmegaCompletePartialOrder α]

/-- abbreviation for omega chain -/
abbrev Chain (α : Type u) [OmegaCompletePartialOrder α] := OmegaCompletePartialOrder.Chain α

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

end QuasiBorelSpaces.OmegaCPO
