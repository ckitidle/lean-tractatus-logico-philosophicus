import Mathlib.Data.Nat.Choose.Sum
import Mathlib.SetTheory.Cardinal.Finite
import Tractatus.LogicalSpace

/-!
# Truth-possibilities, sense, tautology and truth-functions (stage 1)

* the sense of a proposition is represented by the set of truth-possibilities it agrees
  with (4.2),
* counting truth-possibilities and truth-functions (4.27, 4.42, 5.101),
* tautology and contradiction (4.46).
-/

namespace Tractatus

/-- The sense of a proposition: its agreement and disagreement with the possibilities of
existence and non-existence of atomic facts, represented by the set of realities
(truth-possibilities) with which it agrees. -/
@[tlp "4.2"]
abbrev Sense (Atom : Type*) := Set (Reality Atom)

variable {Atom : Type*}

/-- If atomic facts are independent, then for `n` atomic facts there are
`K_n = ∑_{ν=0}^{n} (n choose ν)` possibilities of existence and non-existence
(which equals `2 ^ n`): every combination is possible. -/
@[tlp "4.27"]
theorem card_possible_of_independent [Finite Atom] {L : LogicalSpace Atom}
    (h : Independent L) :
    Nat.card L.possible = ∑ ν ∈ Finset.range (Nat.card Atom + 1), (Nat.card Atom).choose ν := by
  rw [Nat.sum_range_choose, h, Nat.card_univ, Nat.card_fun]
  simp

/-- A proposition (given by its sense) is a tautology if it is true for every
truth-possibility. -/
@[tlp "4.46"]
def IsTautology (p : Sense Atom) : Prop :=
  ∀ r, r ∈ p

/-- A proposition (given by its sense) is a contradiction if it is false for every
truth-possibility. -/
@[tlp "4.46"]
def IsContradiction (p : Sense Atom) : Prop :=
  ∀ r, r ∉ p

/-- A truth-function of `n` elementary propositions, in the manner of the schema of 5.101:
it assigns true or false to each row, i.e. to each truth-possibility of the `n`
arguments. -/
@[tlp "5.101"]
abbrev TruthFunction (n : ℕ) := (Fin n → Bool) → Bool

/-- The truth-grounds of a truth-function: those truth-possibilities of its
truth-arguments which verify it. -/
@[tlp "5.101"]
def truthGrounds {n : ℕ} (f : TruthFunction n) : Set (Fin n → Bool) :=
  {r | f r = true}

/-- For `n` elementary propositions there are `L_n = ∑_{κ=0}^{K_n} (K_n choose κ)`
ways for a proposition to agree and disagree with their truth-possibilities, where
`K_n = 2 ^ n` (so `L_n = 2 ^ (2 ^ n)`). -/
@[tlp "4.42"]
theorem card_truthFunction (n : ℕ) :
    Nat.card (TruthFunction n) = ∑ κ ∈ Finset.range (2 ^ n + 1), (2 ^ n).choose κ := by
  rw [Nat.sum_range_choose]
  simp [TruthFunction]

/-- There are exactly 16 truth-functions of two elementary propositions: the 16 rows of
the schema in 5.101. -/
@[tlp "5.101"]
theorem card_truthFunction_two : Nat.card (TruthFunction 2) = 16 := by
  rw [card_truthFunction, Nat.sum_range_choose]
  norm_num

end Tractatus
