import QuasiBorelSpaces.Bool
import QuasiBorelSpaces.Nat
import QuasiBorelSpaces.ProbabilityMeasure
import QuasiBorelSpaces.Pi
import QuasiBorelSpaces.OmegaCompletePartialOrder.Basic
import QuasiBorelSpaces.OmegaCompletePartialOrder.Fix

set_option linter.missingDocs false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false

/-!
# Contextual Distributions

This file implements the contextual distribution monad:
distributions that are parameterised by an _environment_ of labelled
coin flips.  The construction is the `Reader` monad transformer applied to the
probability monad.
-/

namespace QuasiBorelSpace

/-! ## Basic definitions -/

/-- labels for the contextual randomness source -/
abbrev Label : Type := ℕ

/-- an environment records the Boolean choice associated with each `Label` -/
abbrev Env : Type := Label → Bool

/-- a contextual distribution is a probability distribution that can read from
an environment -/
abbrev CDist (α : Type*) [QuasiBorelSpace α] :=
  Env → ProbabilityMeasure α

variable {α β : Type*} [QuasiBorelSpace α] [QuasiBorelSpace β]

/-! ### Monad-style operations -/

/-- return for contextual distributions: a Dirac distribution, independent of the environment -/
noncomputable def pure (x : α) : CDist α := fun _ => ProbabilityMeasure.unit x

/-- bind for contextual distributions: delegate to the underlying probability bind after
threading the environment -/
noncomputable def bind (x : CDist α) (f : α → CDist β) : CDist β :=
  fun ρ => ProbabilityMeasure.bind (fun a => f a ρ) (x ρ)

scoped notation:55 x " >>=ᶜ " f => bind x f
scoped notation "pureᶜ" => pure

/-! ## Operations -/

/-- read the Boolean associated with label `l` from the environment -/
noncomputable def choose (l : Label) : CDist Bool :=
  fun env => ProbabilityMeasure.unit (env l)

@[simp] lemma choose_apply (l : Label) (ρ : Env) :
    choose l ρ = ProbabilityMeasure.unit (ρ l) := rfl

/-- a simple commutativity law → reading two distinct labels commutes -/
lemma choose_comm
    (l k : Label) (f : Bool → Bool → CDist α)
    : bind (choose l) (fun b => bind (choose k) (f b))
      = bind (choose k) (fun b' => bind (choose l) (fun b => f b b')) := by
  funext ρ
  have hinner (b : Bool) :
      ProbabilityMeasure.bind (fun b' : Bool => f b b' ρ) (ProbabilityMeasure.unit (ρ k))
        = f b (ρ k) ρ := by
    have hhom : IsHom (fun b' : Bool => f b b' ρ) := by fun_prop
    simp [ProbabilityMeasure.bind_unit, hhom]
  have houter :
      ProbabilityMeasure.bind (fun b : Bool => f b (ρ k) ρ) (ProbabilityMeasure.unit (ρ l))
        = f (ρ l) (ρ k) ρ := by
    have hhom : IsHom (fun b : Bool => f b (ρ k) ρ) := by fun_prop
    simp [ProbabilityMeasure.bind_unit, hhom]
  simp [choose, bind, hinner, houter]

/-! ## Shrinking Primitives (Environment Manipulation) -/

/-- update an environment `ρ` at label `l` to value `b` -/
def Env.update (ρ : Env) (l : Label) (b : Bool) : Env :=
  fun k => if k = l then b else ρ k

/-- the masking operator → run `x` as if label `l` implies value `b`
which is the semantic basis for shrinking (forcing a choice) and allows
reasoning about specific random choices in isolation (Theorem 4.7 in the `halcheck` paper) -/
def mask (l : Label) (b : Bool) (x : CDist α) : CDist α :=
  fun ρ => x (Env.update ρ l b)

@[simp]
lemma mask_pure (l : Label) (b : Bool) (a : α) :
    mask l b (pure a) = pure a := rfl

@[simp]
lemma mask_bind (l : Label) (b : Bool) (x : CDist α) (f : α → CDist β) :
    mask l b (x >>=ᶜ f) = bind (mask l b x) (fun a => mask l b (f a)) := by
  funext ρ
  rfl

/-! ### Interaction Laws -/

/-- interaction law: masking the same label forces the result
which corresponds to isolating a specific random variable -/
@[simp]
lemma mask_choose_self (l : Label) (b : Bool) :
    mask l b (choose l) = pure b := by
  funext ρ
  simp [mask, choose, Env.update, pure]

/-- independence law: masking a different label has no effect
this justifies the commutativity of choices with different labels -/
lemma mask_choose_diff {l k : Label} (h : l ≠ k) (b : Bool) :
    mask l b (choose k) = choose k := by
  funext ρ
  have hkl : k ≠ l := fun hkl => h hkl.symm
  simp [mask, choose, Env.update, hkl]

/-- contextual equivalence: `x` and `y` are equivalent with respect to labels in `L`
    this means they behave the same when the environment is restricted to `L`
    (labels outside `L` are set to a default value, here false) -/
def JointEquiv (L : Set Label) (x y : CDist α) : Prop :=
  ∀ ρ, (∀ l ∉ L, ρ l = false) → x ρ = y ρ

scoped notation:50 x " ⊜[" L "] " y => JointEquiv L x y

lemma jointEquiv_refl (L : Set Label) (x : CDist α) : x ⊜[L] x :=
  fun _ _ => rfl

lemma jointEquiv_symm {L : Set Label} {x y : CDist α} (h : x ⊜[L] y) : y ⊜[L] x :=
  fun ρ hρ => (h ρ hρ).symm

lemma jointEquiv_trans {L : Set Label} {x y z : CDist α} (h1 : x ⊜[L] y) (h2 : y ⊜[L] z) :
    x ⊜[L] z :=
  fun ρ hρ => (h1 ρ hρ).trans (h2 ρ hρ)

lemma jointEquiv_mono {L K : Set Label} (hLK : L ⊆ K) {x y : CDist α} (h : x ⊜[K] y) : x ⊜[L] y :=
  fun ρ hρ => h ρ (fun l hl => hρ l (fun hInL => hl (hLK hInL)))

/-! ## Recursion -/

open OmegaCompletePartialOrder

/-- the fixed-point combinator for `CDist`
    note: this requires `OrderBot (CDist α)` which is currently not satisfied
    because `ProbabilityMeasure` does not have a bottom element
    but we provide the definition for future use if `CDist` is extended -/
def fix [OrderBot (CDist α)] (f : CDist α →𝒄 CDist α) : CDist α :=
  OmegaCompletePartialOrder.fix f

/-- fixed point property -/
lemma fix_eq [OrderBot (CDist α)] (f : CDist α →𝒄 CDist α) : fix f = f (fix f) :=
  OmegaCompletePartialOrder.fix_eq f

/-! ## Fundamental Theorems -/

-- commutativity and other properties can go here later if we need them

end QuasiBorelSpace
