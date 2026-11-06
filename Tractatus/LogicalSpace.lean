import Mathlib.Data.Set.Basic
import Mathlib.Logic.Equiv.Defs
import Tractatus.Meta

/-!
# Atomic facts, the world, reality and logical space (stage 1)

The atomic facts (*Sachverhalte*) are a type parameter `Atom`: what they are is not settled
a priori (5.557), so we only assume that there is a type of them.

* the world is the set of atomic facts that exist (2.04),
* reality is the assignment of existence/non-existence to every atomic fact (2.06),
* a logical space is a set of such assignments that count as possible,
* independence of atomic facts (2.061) is the condition that every assignment is possible.

Readings adopted here are recorded in analysis/interpretation.md (independence,
world_reality) and in correspondence/stage1.md.
-/

namespace Tractatus

variable (Atom : Type*)

/-- The world, represented as the set of those atomic facts that obtain. -/
@[tlp "2.04"]
abbrev World := Set Atom

/-- Reality, represented as a choice, for every atomic fact, of whether it obtains
(`true`, a positive fact) or not (`false`, a negative fact). We also use this as a
truth-possibility of the elementary propositions (4.3). -/
@[tlp "2.06"]
abbrev Reality := Atom → Bool

/-- A logical space: the realities (choices of which atomic facts obtain) that count as
possible at all. -/
structure LogicalSpace where
  /-- the possible assignments -/
  possible : Set (Reality Atom)

variable {Atom}

/-- The claim of independence, read here as: whichever atomic facts obtain and whichever
do not, that combination is possible. This is a condition on a logical space, used as a
hypothesis by the theorems that depend on it. -/
@[tlp "2.061"]
def Independent (L : LogicalSpace Atom) : Prop :=
  L.possible = Set.univ

/-- Once the world is given, the atomic facts that do not obtain are fixed as well: they
are exactly the complement of the world. (This holds by the definition of the world as a
set.) -/
@[tlp "2.05"]
theorem nonexistent_eq_compl (w : World Atom) : {a | a ∉ w} = wᶜ :=
  rfl

open Classical in
/-- The one-to-one correspondence between the world (a set of atomic facts) and reality
(a choice, for each atomic fact, of whether it obtains). -/
noncomputable def worldEquivReality : World Atom ≃ Reality Atom where
  toFun w a := decide (a ∈ w)
  invFun r := {a | r a = true}
  left_inv w := by ext a; simp
  right_inv r := by funext a; simp

/-- The world and reality determine each other: they correspond one-to-one. We read the
identification of the whole of reality with the world in this sense. -/
@[tlp "2.063"]
theorem world_equiv_reality : Nonempty (World Atom ≃ Reality Atom) :=
  ⟨worldEquivReality⟩

/-- Under independence, two distinct atomic facts can take any pair of values in some
possible reality. -/
theorem exists_possible_of_independent {L : LogicalSpace Atom} (h : Independent L)
    {a b : Atom} (hab : a ≠ b) (x y : Bool) :
    ∃ r ∈ L.possible, r a = x ∧ r b = y := by
  classical
  refine ⟨fun c => if c = a then x else y, ?_, by simp, by simp [Ne.symm hab]⟩
  rw [h]
  exact Set.mem_univ _

/-- Under independence, whether one atomic fact obtains settles nothing about whether a
different one obtains: for no values `x`, `y` does "`a` has value `x`" entail "`b` has
value `y`" across all possible realities. -/
@[tlp "2.062"]
theorem no_inference_between_atomic_facts {L : LogicalSpace Atom} (h : Independent L)
    {a b : Atom} (hab : a ≠ b) (x y : Bool) :
    ¬ ∀ r ∈ L.possible, r a = x → r b = y := by
  intro hall
  obtain ⟨r, hr, hra, hrb⟩ := exists_possible_of_independent h hab x (!y)
  have := hall r hr hra
  rw [hrb] at this
  cases y <;> simp at this

end Tractatus
