import Mathlib.Order.SetNotation
import Mathlib.Data.Set.Finite.Basic
import Tractatus.LogicalSpace

/-!
# Facts and the world (stage 1: 1–1.21, 2)

* a fact is the existence of some atomic facts, represented by the set of those atomic
  facts (2),
* the facts of a world are the sets of atomic facts that all obtain in it (1, 1.1); the world
  is recovered from them and determined by them (1.11, 1.12), and divides into them (1.2),
* the worlds in a logical space (1.13),
* the claim 1.21 that any single atomic fact can change while everything else stays the
  same, and how it relates to independence (2.061).
-/

namespace Tractatus

variable {Atom : Type*}

/-- A fact, as the existence of some atomic facts: represented by the set of the atomic
facts whose existence it consists in. -/
@[tlp "2"]
abbrev Fact (Atom : Type*) := Set Atom

/-- The facts of a world: the facts all of whose atomic facts obtain in it. The world is
taken as the totality of these facts (not of objects: a fact is made of atomic facts). -/
@[tlp "1", tlp "1.1"]
def World.facts (w : World Atom) : Set (Fact Atom) :=
  {f | f ⊆ w}

/-- The world is recovered as the union of its facts. -/
@[tlp "1.1"]
theorem World.sUnion_facts (w : World Atom) : Set.sUnion (World.facts w) = w := by
  apply Set.Subset.antisymm
  · intro a ⟨f, hf, ha⟩
    exact hf ha
  · intro a ha
    exact ⟨{a}, Set.singleton_subset_iff.mpr ha, rfl⟩

/-- The world is determined by its facts: two worlds with the same facts are the same. That
these are *all* the facts is built into taking the facts of a world as a set. -/
@[tlp "1.11"]
theorem World.facts_injective : Function.Injective (World.facts (Atom := Atom)) := by
  intro w w' h
  rw [← World.sUnion_facts w, ← World.sUnion_facts w', h]

/-- The totality of facts also fixes what is not the case: the atomic facts outside every
fact of the world are exactly those not in the world. -/
@[tlp "1.12"]
theorem World.not_case_eq_compl (w : World Atom) :
    {a | a ∉ Set.sUnion (World.facts w)} = wᶜ := by
  rw [World.sUnion_facts]
  rfl

/-- The world divides into facts: it is the union of the single-atomic-fact facts it
contains. -/
@[tlp "1.2"]
theorem World.eq_sUnion_singleton_facts (w : World Atom) :
    w = Set.sUnion {f ∈ World.facts w | ∃ a, f = {a}} := by
  apply Set.Subset.antisymm
  · intro a ha
    exact ⟨{a}, ⟨Set.singleton_subset_iff.mpr ha, a, rfl⟩, rfl⟩
  · intro a ⟨f, ⟨hf, _⟩, ha⟩
    exact hf ha

open Classical in
/-- The worlds in a logical space: those worlds whose corresponding reality is possible. -/
@[tlp "1.13"]
noncomputable def LogicalSpace.worlds (L : LogicalSpace Atom) : Set (World Atom) :=
  {w | worldEquivReality w ∈ L.possible}

/-- The claim that any single atomic fact can obtain or not while everything else stays the
same: switching the value of one atomic fact in a possible reality gives a possible
reality. -/
@[tlp "1.21"]
def CanVaryAlone [DecidableEq Atom] (L : LogicalSpace Atom) : Prop :=
  ∀ r ∈ L.possible, ∀ a, Function.update r a (!r a) ∈ L.possible

/-- Independence (2.061) implies that each atomic fact can vary alone. -/
@[tlp "1.21"]
theorem canVaryAlone_of_independent [DecidableEq Atom] {L : LogicalSpace Atom} (h : Independent L) :
    CanVaryAlone L := by
  intro r _ a
  rw [h]
  exact Set.mem_univ _

/-- With finitely many atomic facts, the converse holds as well: if some reality is
possible and each atomic fact can vary alone, then every reality is possible, since any
reality is reached by switching finitely many atomic facts one at a time. (With
infinitely many atomic facts this fails; see `Models.canVaryAlone_not_independent`.) -/
@[tlp "1.21"]
theorem independent_of_canVaryAlone [Finite Atom] [DecidableEq Atom] {L : LogicalSpace Atom}
    (h : CanVaryAlone L) (hne : L.possible.Nonempty) : Independent L := by
  obtain ⟨r₀, h₀⟩ := hne
  suffices key : ∀ (s : Finset Atom) (r : Reality Atom), r ∈ L.possible →
      ∀ r' : Reality Atom, (∀ a, a ∉ s → r' a = r a) → r' ∈ L.possible by
    rw [Independent, Set.eq_univ_iff_forall]
    intro r'
    exact key (Set.toFinite Set.univ).toFinset r₀ h₀ r' (by simp)
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro r hr r' hr'
    have : r' = r := funext fun a => hr' a (Finset.notMem_empty a)
    rw [this]
    exact hr
  | insert a s ha ih =>
    intro r hr r' hr'
    by_cases hra : r' a = r a
    · refine ih r hr r' fun b hb => ?_
      by_cases hba : b = a
      · rw [hba]; exact hra
      · exact hr' b (by simp [hba, hb])
    · refine ih _ (h r hr a) r' fun b hb => ?_
      by_cases hba : b = a
      · rw [hba, Function.update_self]
        cases hr : r a <;> cases hr' : r' a <;> simp_all
      · rw [Function.update_of_ne hba]
        exact hr' b (by simp [hba, hb])

end Tractatus
