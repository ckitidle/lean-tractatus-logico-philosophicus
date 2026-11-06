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

/-- The world: the totality of existent atomic facts, i.e. the set of atomic facts
that exist. -/
@[tlp "2.04"]
abbrev World := Set Atom

/-- Reality: for every atomic fact, whether it exists (`true`) or not (`false`).
The existence of an atomic fact is a positive fact, its non-existence a negative fact.
The same object is a truth-possibility of the elementary propositions (4.3). -/
@[tlp "2.06"]
abbrev Reality := Atom → Bool

/-- A logical space: the realities (assignments of existence and non-existence to atomic
facts) that are possible at all. -/
structure LogicalSpace where
  /-- the possible assignments -/
  possible : Set (Reality Atom)

variable {Atom}

/-- The claim that atomic facts are independent of one another: every combination of
existence and non-existence of atomic facts is possible. This is a condition on a logical
space, used as a hypothesis by the theorems that depend on it. -/
@[tlp "2.061"]
def Independent (L : LogicalSpace Atom) : Prop :=
  L.possible = Set.univ

/-- The totality of existent atomic facts also determines which atomic facts do not exist:
the non-existent ones are exactly the complement of the world.
(This holds by the definition of the world as a set.) -/
@[tlp "2.05"]
theorem nonexistent_eq_compl (w : World Atom) : {a | a ∉ w} = wᶜ :=
  rfl

open Classical in
/-- The one-to-one correspondence between the world (the existent atomic facts) and
reality (existence and non-existence of every atomic fact). -/
noncomputable def worldEquivReality : World Atom ≃ Reality Atom where
  toFun w a := decide (a ∈ w)
  invFun r := {a | r a = true}
  left_inv w := by ext a; simp
  right_inv r := by funext a; simp

/-- The world (existence of atomic facts) and reality (existence and non-existence of
atomic facts) determine each other: they correspond one-to-one. We read the identification
of the total reality with the world in this sense. -/
@[tlp "2.063"]
theorem world_equiv_reality : Nonempty (World Atom ≃ Reality Atom) :=
  ⟨worldEquivReality⟩

/-- Under independence, any combination of existence and non-existence of two distinct
atomic facts is possible. -/
theorem exists_possible_of_independent {L : LogicalSpace Atom} (h : Independent L)
    {a b : Atom} (hab : a ≠ b) (x y : Bool) :
    ∃ r ∈ L.possible, r a = x ∧ r b = y := by
  classical
  refine ⟨fun c => if c = a then x else y, ?_, by simp, by simp [Ne.symm hab]⟩
  rw [h]
  exact Set.mem_univ _

/-- If atomic facts are independent, then from the existence or non-existence of one
atomic fact nothing can be inferred about the existence or non-existence of another:
for no values `x`, `y` does "`a` has value `x`" entail "`b` has value `y`" across all
possible realities. -/
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
