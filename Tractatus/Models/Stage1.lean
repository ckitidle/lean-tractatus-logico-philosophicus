import Mathlib.Data.Fin.Basic
import Mathlib.Data.Set.Finite.Basic
import Tractatus.Objects
import Tractatus.Consequence

/-!
# Models for stage 1

* consistency: a logical space satisfying the claim of independence (2.061) exists for any
  type of atomic facts; one model satisfies all the claims of stage 1 together
  (`stage1_consistent`), so the hypotheses of the stage-1 theorems are not contradictory;
* counter-models:
  * without independence, an inference between atomic facts can be valid, so 2.062 really
    depends on 2.061, and a picture can be true a priori (2.225),
  * with infinitely many atomic facts, each atomic fact can vary alone (1.21) without
    every combination being possible (2.061).
-/

namespace Tractatus.Models

open Tractatus

/-- The full logical space: every reality is possible. -/
def fullSpace (Atom : Type*) : LogicalSpace Atom :=
  ⟨Set.univ⟩

/-- The claim of independence is satisfiable: the full logical space satisfies it. -/
@[tlp "2.061"]
theorem fullSpace_independent (Atom : Type*) : Independent (fullSpace Atom) :=
  rfl

/-- Without independence, an inference between atomic facts can be valid: in a logical
space with two atomic facts that always have the same value, the existence of the first
entails the existence of the second. So the conclusion of 2.062 needs the claim of
2.061. -/
@[tlp "2.062"]
theorem inference_possible_without_independence :
    ∃ L : LogicalSpace (Fin 2), ¬ Independent L ∧ ∀ r ∈ L.possible, r 0 = true → r 1 = true := by
  refine ⟨⟨{r | r 0 = r 1}⟩, ?_, ?_⟩
  · intro h
    change ({r | r 0 = r 1} : Set (Fin 2 → Bool)) = Set.univ at h
    have hmem : (fun i : Fin 2 => decide (i = 0)) ∈ ({r | r 0 = r 1} : Set (Fin 2 → Bool)) := by
      rw [h]; exact Set.mem_univ _
    simp at hmem
  · intro r hr h0
    simp only [Set.mem_ofPred_eq] at hr
    rw [← hr]
    exact h0

/-- Without independence, a picture can be true a priori: in a logical space with a single
possible reality, a picture true in it is true in every possible reality. So 2.225 depends
on 2.061. -/
@[tlp "2.225"]
theorem apriori_true_without_independence :
    ∃ (L : LogicalSpace (Fin 1)) (p : Picture (Fin 1)), ∀ r ∈ L.possible, p.IsTrue r := by
  refine ⟨⟨{fun _ => true}⟩, ⟨fun _ => some true, ⟨0, rfl⟩⟩, ?_⟩
  rintro r rfl a b hab
  simp only [Option.some.injEq] at hab
  exact hab

/-- The logical space of the realities in which only finitely many atomic facts obtain. -/
def finiteSupportSpace : LogicalSpace ℕ :=
  ⟨{r | {n | r n = true}.Finite}⟩

/-- With infinitely many atomic facts, each atomic fact can vary alone (1.21) although not
every combination is possible (2.061 fails): in `finiteSupportSpace`, switching one atomic
fact keeps the set of obtaining atomic facts finite, but the reality in which all obtain is
not possible. So 1.21 is weaker than 2.061 (they agree for finitely many atomic facts,
`independent_of_canVaryAlone`). -/
@[tlp "1.21"]
theorem canVaryAlone_not_independent :
    CanVaryAlone finiteSupportSpace ∧ ¬ Independent finiteSupportSpace := by
  constructor
  · intro r hr a
    refine (hr.insert a).subset fun n hn => ?_
    by_cases hna : n = a
    · exact Or.inl hna
    · simp only [Set.mem_ofPred_eq, Function.update_of_ne hna] at hn
      exact Or.inr hn
  · intro h
    have hmem : (fun _ => true : Reality ℕ) ∈ finiteSupportSpace.possible := by
      rw [h]; exact Set.mem_univ _
    exact Set.infinite_univ (by simpa [finiteSupportSpace] using hmem)

/-- The frame in which every configuration is a possible atomic fact. -/
def fullFrame (Object Mode : Type*) : Frame Object Mode :=
  ⟨Set.univ⟩

/-- In the full frame (with at least one mode of combination), the claims about objects hold:
their forms settle all possibilities (2.0123, 2.014, 2.023), every object can occur in an
atomic fact (2.011), and objects of the same form are interchangeable (2.0233). -/
@[tlp "2.0123", tlp "2.011", tlp "2.0233"]
theorem fullFrame_claims (Object Mode : Type*) [Nonempty Mode] :
    (fullFrame Object Mode).FormDeterminesPossibility ∧
      (fullFrame Object Mode).EveryObjectCanOccur ∧
      (fullFrame Object Mode).SameFormInterchangeable := by
  have h1 : (fullFrame Object Mode).FormDeterminesPossibility := fun _ _ => Set.mem_univ _
  refine ⟨h1, fun o => ?_, Frame.sameFormInterchangeable_of_formDeterminesPossibility _ h1⟩
  let m : Mode := Classical.arbitrary Mode
  exact ⟨(m, 1, 0), ⟨m, [o], by simp⟩, Set.mem_univ _, 0, by simp, rfl, rfl⟩

open Classical in
/-- One model satisfies all the claims of stage 1 together: two objects, one mode of
combination, every configuration a possible atomic fact, every reality possible, and as
language the truth-functions of elementary propositions. So the claims are jointly
consistent. -/
@[tlp "2.061", tlp "1.21", tlp "2.203", tlp "4.211", tlp "5", tlp "5.634"]
theorem stage1_consistent :
    let F := fullFrame (Fin 2) Unit
    let L := fullSpace (AtomicFact (Fin 2) Unit)
    (F.FormDeterminesPossibility ∧ F.EveryObjectCanOccur ∧ F.SameFormInterchangeable) ∧
      Independent L ∧ CanVaryAlone L ∧ (∀ p : Picture _, p.ContainsPossibility L) ∧
      ElementaryCompatible L ∧ ExtensionalityThesis {p : Sense (AtomicFact (Fin 2) Unit) | IsTruthFunctionOfElementary p} ∧
      CouldBeOtherwise L := by
  intro F L
  have hL : Independent L := fullSpace_independent _
  exact ⟨fullFrame_claims _ _, hL, canVaryAlone_of_independent hL,
    fun p => p.containsPossibility_of_independent hL, elementaryCompatible_of_independent hL,
    fun _ hp => hp, couldBeOtherwise_of_independent hL⟩

end Tractatus.Models
