import Tractatus.Names

/-!
# Internal properties (stage 3: 4.122–4.125)

* an internal property is one that it is unthinkable its bearer should lack: it holds in every
  possible reality (4.123); a feature is an internal property of a fact (4.1221),
* a formal property of objects depends only on their form (4.122),
* an internal relation between possible situations shows itself as an internal relation
  (consequence) between the propositions (4.125).
-/

namespace Tractatus

variable {Atom Object Mode : Type*}

/-- An internal property of `x` (in a logical space): it is unthinkable that `x` should not have
it, i.e. it holds of `x` in every possible reality. -/
@[tlp "4.123"]
def IsInternalProperty {α : Type*} (L : LogicalSpace Atom) (P : Reality Atom → α → Prop)
    (x : α) : Prop :=
  ∀ r ∈ L.possible, P r x

/-- A feature of a fact: an internal property of it. -/
@[tlp "4.1221"]
def IsFeature (L : LogicalSpace Atom) (P : Reality Atom → Fact Atom → Prop) (f : Fact Atom) :
    Prop :=
  IsInternalProperty L P f

/-- A formal property of objects: one that depends only on their form, so that objects of the
same form have it alike. -/
@[tlp "4.122"]
def IsFormalProperty (F : Frame Object Mode) (P : Object → Prop) : Prop :=
  ∀ o o', F.form o = F.form o' → (P o ↔ P o')

/-- The holding of an internal property is not something a significant proposition could
assert: the proposition that `x` has it is certain in the logical space, hence says nothing
about which possible reality obtains. -/
@[tlp "4.122", tlp "4.123"]
theorem certainIn_of_internal {α : Type*} {L : LogicalSpace Atom} {P : Reality Atom → α → Prop}
    {x : α} (h : IsInternalProperty L P x) : CertainIn L {r | P r x} :=
  fun r hr => h r hr

/-- The internal relation between the situations two pictures represent (one region of logical
space contained in the other) is the internal relation of consequence between the
propositions. -/
@[tlp "4.125"]
theorem region_subset_iff_follows {L : LogicalSpace Atom} (p q : Picture Atom) :
    q.region L ⊆ p.region L ↔ Follows L p.sense q.sense :=
  follows_iff_subset.symm

end Tractatus
