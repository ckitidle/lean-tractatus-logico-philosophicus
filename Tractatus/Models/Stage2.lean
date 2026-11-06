import Tractatus.Logic
import Tractatus.Operation
import Tractatus.Models.Stage1

/-!
# Models for stage 2

* consistency: the claims of stage 2 (the general form of proposition, 5.3 / 6.001, and that
  the only necessity and impossibility are logical, 6.37, 6.375) hold together in one model;
* a counter-model: without independence, something can be necessary without being a
  tautology, and impossible without being a contradiction.
-/

namespace Tractatus.Models

open Tractatus

/-- One model satisfies the claims of stage 2 together: every reality possible, and as
language the senses of the signs of the general form. -/
@[tlp "5.3", tlp "6.37", tlp "6.375"]
theorem stage2_consistent :
    let L := fullSpace (Fin 2)
    GeneralFormThesis (Set.range (Formula.sense (Atom := Fin 2))) ∧
      OnlyLogicalNecessity L ∧ OnlyLogicalImpossibility L := by
  intro L
  have hL : Independent L := fullSpace_independent _
  exact ⟨fun _ ⟨φ, hφ⟩ => ⟨φ, hφ⟩, onlyLogicalNecessity_of_independent hL,
    onlyLogicalImpossibility_of_independent hL⟩

/-- Without independence, there is non-logical necessity and impossibility: in a logical
space with a single possible reality, the elementary proposition true in it is certain but not
a tautology, and its denial is impossible but not a contradiction. -/
@[tlp "6.37", tlp "6.375"]
theorem nonlogical_necessity_without_independence :
    ∃ L : LogicalSpace (Fin 1),
      ¬ OnlyLogicalNecessity L ∧ ¬ OnlyLogicalImpossibility L := by
  refine ⟨⟨{fun _ => true}⟩, fun h => ?_, fun h => ?_⟩
  · have := h (elementary 0) (by rintro r rfl; rfl) (fun _ => false)
    simp [elementary] at this
  · have := h (elementary 0)ᶜ (by
      ext r
      simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_singleton_iff,
        Set.mem_empty_iff_false, iff_false, not_and]
      rintro hr rfl
      exact hr rfl) (fun _ => false)
    simp [elementary] at this

end Tractatus.Models
