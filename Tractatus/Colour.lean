import Tractatus.Logic

/-!
# The exclusion of colours (stage 3: 6.3751)

6.3751 says that two colours at one place of the visual field is logically impossible (a
contradiction), and that the logical product of two elementary propositions can be neither a
tautology nor a contradiction. Here:

* the second statement is a theorem,
* hence, under the reading that the colour propositions are elementary, their exclusion is not
  a logical impossibility (the claim fails under that reading); and a logical space in which two
  elementary propositions exclude each other violates independence (2.061), the compatibility of
  elementary propositions (4.211) and the claim that only logical impossibility exists (6.375),
* if the colour propositions are analysed as truth-functions of elementary propositions, their
  exclusion can be a contradiction (consistent with independence).
-/

namespace Tractatus

variable {Atom : Type*}

/-- The claim that the exclusion of two colours is a logical impossibility: the logical product
of the two colour propositions is a contradiction. -/
@[tlp "6.3751"]
def ExclusionIsLogical (red green : Sense Atom) : Prop :=
  IsContradiction (red ∩ green)

/-- The logical product of two elementary propositions is neither a tautology nor a
contradiction (this holds even without assuming the two are distinct). -/
@[tlp "6.3751"]
theorem elementary_product_not_senseless [DecidableEq Atom] (a b : Atom) :
    ¬ IsTautology (elementary a ∩ elementary b) ∧ ¬ IsContradiction (elementary a ∩ elementary b) := by
  constructor
  · intro h
    have := (h (fun c => decide (c ≠ b))).2
    simp [elementary] at this
  · intro h
    exact h (fun _ => true) ⟨rfl, rfl⟩

/-- Under the reading that the two colour propositions are elementary propositions, their
exclusion is not a logical impossibility. -/
@[tlp_refutes "6.3751"]
theorem exclusion_not_logical_of_elementary [DecidableEq Atom] (a b : Atom) :
    ¬ ExclusionIsLogical (elementary a) (elementary b) :=
  (elementary_product_not_senseless a b).2

/-- If two elementary propositions exclude each other in a logical space (as the colour
propositions would), that logical space is not independent, its elementary propositions are not
all compatible, and it has an impossibility that is not logical. -/
@[tlp "6.3751"]
theorem elementary_exclusion_conflicts [DecidableEq Atom] {L : LogicalSpace Atom} {a b : Atom}
    (hex : ImpossibleIn L (elementary a ∩ elementary b)) :
    ¬ Independent L ∧ ¬ ElementaryCompatible L ∧ ¬ OnlyLogicalImpossibility L := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => (exclusion_not_logical_of_elementary a b) (h _ hex)⟩
  · have : (fun _ => true : Reality Atom) ∈ elementary a ∩ elementary b ∩ L.possible :=
      ⟨⟨rfl, rfl⟩, by rw [h]; exact Set.mem_univ _⟩
    rw [hex] at this
    exact this
  · obtain ⟨r, hr⟩ := h a b
    rw [ImpossibleIn] at hex
    rw [hex] at hr
    exact hr

/-- If the colour propositions are analysed as truth-functions of elementary propositions (here
"red" as the first elementary proposition and "green" as "not the first, and the second"), their
exclusion is a contradiction, and both can be true. -/
@[tlp "6.3751"]
theorem exclusion_logical_of_analysed :
    ExclusionIsLogical (elementary (0 : Fin 2)) ((elementary 0)ᶜ ∩ elementary 1) ∧
      (elementary (0 : Fin 2)).Nonempty ∧ ((elementary (0 : Fin 2))ᶜ ∩ elementary 1).Nonempty := by
  refine ⟨fun r ⟨h0, h0', _⟩ => h0' h0, ⟨fun _ => true, rfl⟩, ⟨fun i => decide (i = 1), ?_, ?_⟩⟩
  · simp [elementary]
  · simp [elementary]

end Tractatus
