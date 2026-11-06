import Mathlib.Data.Fin.Basic
import Tractatus.LogicalSpace

/-!
# Models for stage 1

* consistency: a logical space satisfying the claim of independence (2.061) exists for any
  type of atomic facts, so the hypothesis of the stage-1 theorems is not contradictory;
* a counter-model: without independence, an inference between atomic facts can be valid,
  so 2.062 really depends on 2.061.
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

end Tractatus.Models
