import Mathlib.Order.OmegaCompletePartialOrder

/-
Faithful ωCPO structure on `Option α` (bottom element `none`, supremum of a chain
given by the first defined element and the ω-supremum of the tail).
-/

namespace OmegaCompletePartialOrder

noncomputable section

variable {α : Type*} [OmegaCompletePartialOrder α]

/-- Bottom-order on options: `none` is bottom, `some` is ordered pointwise. -/
instance : PartialOrder (Option α) where
  le x y :=
    match x, y with
    | none, _ => True
    | some _, none => False
    | some a, some b => a ≤ b
  lt x y :=
    match x, y with
    | none, some _ => True
    | some a, some b => a < b
    | _, _ => False
  le_refl
    | none => trivial
    | some _ => le_rfl
  le_trans
    | none, _, _, _ , _ => trivial
    | some _, none, _, h, _ => False.elim h
    | some _, some _, none, _, hyz => False.elim hyz
    | some a, some b, some c, h1, h2 => le_trans h1 h2
  le_antisymm
    | none, none, _, _ => rfl
    | none, some _, _, hyx => False.elim hyx
    | some _, none, hxy, _ => False.elim hxy
    | some a, some b, hxy, hyx => congrArg some (le_antisymm hxy hyx)
  lt_iff_le_not_ge
    | none, none => by simp
    | none, some _ => by simp
    | some _, none => by simp
    | some a, some b => by simp [lt_iff_le_not_ge]

/-- Pick any index where a chain hits `some` -/
noncomputable def firstSomeIndex (c : Chain (Option α)) (h : ∃ n x, c n = some x) : ℕ :=
  Classical.choose h

/-- A witness that the chain hits `some` at `firstSomeIndex` -/
noncomputable def firstSomeValue (c : Chain (Option α)) (h : ∃ n x, c n = some x) : α :=
  Classical.choose (Classical.choose_spec h)

lemma firstSome_spec (c : Chain (Option α)) (h : ∃ n x, c n = some x) :
    c (firstSomeIndex c h) = some (firstSomeValue c h) := by
  classical
  have := Classical.choose_spec (Classical.choose_spec h)
  simpa using this

/-- Chain of underlying values after the first `some`, padding with the first value -/
noncomputable def tailChain (c : Chain (Option α)) (h : ∃ n x, c n = some x) : Chain α :=
{ toFun := fun k =>
    match c (firstSomeIndex c h + k) with
    | some x => x
    | none => firstSomeValue c h
  monotone' := by
    sorry }

/-- ω-supremum on `Option α`: either `none` for an all-bottom chain,
    or `some` of the ω-supremum of the tail of defined elements -/
noncomputable instance : OmegaCompletePartialOrder (Option α) where
  ωSup c :=
    open Classical in
    if h : ∃ n x, c n = some x then
      some (ωSup (tailChain c h))
    else
      none
  le_ωSup := by
    intro c i
    sorry
  ωSup_le := by
    intro c x hx
    sorry

end

end OmegaCompletePartialOrder
