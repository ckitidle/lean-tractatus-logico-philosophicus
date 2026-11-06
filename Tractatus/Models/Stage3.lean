import Tractatus.Colour
import Tractatus.Models.Stage1

/-!
# Models for stage 3

* consistency: the claim of 6.3751 (the exclusion of colours is a logical impossibility) holds
  together with independence (2.061), when the colour propositions are analysed as
  truth-functions of elementary propositions rather than taken as elementary.
-/

namespace Tractatus.Models

open Tractatus

/-- With two atomic facts and every reality possible, "red" (the first elementary proposition)
and "green" (not the first, and the second) are both possible, and their exclusion is a
contradiction: the claim of 6.3751 is consistent with independence once the colour propositions
are analysed. -/
@[tlp "6.3751"]
theorem stage3_consistent :
    let red : Sense (Fin 2) := elementary 0
    let green : Sense (Fin 2) := (elementary 0)ᶜ ∩ elementary 1
    Independent (fullSpace (Fin 2)) ∧ ExclusionIsLogical red green ∧
      PossibleIn (fullSpace (Fin 2)) red ∧ PossibleIn (fullSpace (Fin 2)) green := by
  intro red green
  obtain ⟨hex, ⟨r, hr⟩, ⟨g, hg⟩⟩ := exclusion_logical_of_analysed
  exact ⟨fullSpace_independent _, hex, ⟨r, hr, Set.mem_univ _⟩, ⟨g, hg, Set.mem_univ _⟩⟩

end Tractatus.Models
