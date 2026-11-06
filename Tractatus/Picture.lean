import Tractatus.TruthPossibility

/-!
# The sense and truth of pictures (stage 1: 2.201–2.225, 4.462, 4.464, 5.634)

Only what a picture represents is formalized here, not how it is built (its elements and
their structure, 2.1–2.19, belong to stage 3).

* a picture represents a possibility of existence and non-existence of atomic facts: some
  atomic facts as existing and some as not existing (2.201); its sense is the set of
  realities agreeing with that (2.221),
* it is true when reality agrees with its sense (2.222),
* under independence (2.061), every picture can be true and can be false, so no picture is
  true a priori (2.224, 2.225, 5.634), and no picture is a tautology or a contradiction
  (4.462).
-/

namespace Tractatus

variable (Atom : Type*)

/-- A picture, as far as what it represents is concerned: it represents some atomic facts as
existing (`some true`) and some as not existing (`some false`), and leaves the rest open
(`none`). It represents at least one atomic fact. -/
@[tlp "2.201"]
structure Picture where
  /-- what the picture represents about each atomic fact -/
  depicts : Atom → Option Bool
  nontrivial : ∃ a, (depicts a).isSome

variable {Atom}

namespace Picture

variable (p : Picture Atom)

/-- The sense of a picture, i.e. what it represents: the realities that agree with it on
every atomic fact it represents. -/
@[tlp "2.221"]
def sense : Sense Atom :=
  {r | ∀ a b, p.depicts a = some b → r a = b}

/-- A picture is true in a reality when its sense agrees with that reality. -/
@[tlp "2.222"]
def IsTrue (r : Reality Atom) : Prop :=
  r ∈ p.sense

/-- In each reality, a picture is either true or false, and not both. -/
@[tlp "2.21"]
theorem isTrue_or_not (r : Reality Atom) : (p.IsTrue r ∨ ¬ p.IsTrue r) ∧ ¬ (p.IsTrue r ∧ ¬ p.IsTrue r) :=
  ⟨em _, fun h => h.2 h.1⟩

/-- The region of logical space a picture represents: the possible realities agreeing with
it. -/
@[tlp "2.202"]
def region (L : LogicalSpace Atom) : Set (Reality Atom) :=
  p.sense ∩ L.possible

/-- The claim that a picture contains the possibility of what it represents: some possible
reality agrees with it. -/
@[tlp "2.203"]
def ContainsPossibility (L : LogicalSpace Atom) : Prop :=
  (p.region L).Nonempty

/-- A reality that makes the picture true. -/
def witness : Reality Atom :=
  fun a => (p.depicts a).getD false

theorem witness_isTrue : p.IsTrue p.witness := by
  intro a b h
  simp [witness, h]

/-- Under independence, every picture contains the possibility of what it represents. -/
@[tlp "2.203"]
theorem containsPossibility_of_independent {L : LogicalSpace Atom} (h : Independent L) :
    p.ContainsPossibility L :=
  ⟨p.witness, p.witness_isTrue, by rw [h]; exact Set.mem_univ _⟩

/-- Whether a picture is true is decided by comparing it with reality: it depends only on
the atomic facts it represents, and on what reality says about them. -/
@[tlp "2.223"]
theorem isTrue_congr {r r' : Reality Atom}
    (h : ∀ a, (p.depicts a).isSome → r a = r' a) : p.IsTrue r ↔ p.IsTrue r' := by
  have key : ∀ {r r' : Reality Atom}, (∀ a, (p.depicts a).isSome → r a = r' a) →
      p.IsTrue r → p.IsTrue r' := by
    intro r r' h hr a b hab
    rw [← h a (by simp [hab])]
    exact hr a b hab
  exact ⟨key h, key fun a ha => (h a ha).symm⟩

/-- Under independence, the picture alone does not decide whether it is true: some possible
reality makes it true and another makes it false. -/
@[tlp "2.224"]
theorem exists_true_and_false {L : LogicalSpace Atom} (h : Independent L) :
    (∃ r ∈ L.possible, p.IsTrue r) ∧ ∃ r ∈ L.possible, ¬ p.IsTrue r := by
  classical
  refine ⟨⟨p.witness, by rw [h]; exact Set.mem_univ _, p.witness_isTrue⟩, ?_⟩
  obtain ⟨a, ha⟩ := p.nontrivial
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp ha
  refine ⟨Function.update p.witness a (!b), by rw [h]; exact Set.mem_univ _, fun ht => ?_⟩
  have := ht a b hb
  rw [Function.update_self] at this
  cases b <;> simp at this

/-- Under independence, no picture is true a priori, i.e. true in every possible reality. -/
@[tlp "2.225"]
theorem not_apriori_true {L : LogicalSpace Atom} (h : Independent L) :
    ¬ ∀ r ∈ L.possible, p.IsTrue r := by
  obtain ⟨r, hr, hf⟩ := (p.exists_true_and_false h).2
  exact fun hall => hf (hall r hr)

/-- No picture is a tautology or a contradiction: its sense is neither everything nor
nothing (it allows some state of affairs and excludes some). -/
@[tlp "4.462"]
theorem sense_not_senseless : ¬ IsTautology p.sense ∧ ¬ IsContradiction p.sense := by
  have h := p.exists_true_and_false (L := ⟨Set.univ⟩) rfl
  obtain ⟨⟨r, _, hr⟩, ⟨r', _, hr'⟩⟩ := h
  exact ⟨fun ht => hr' (ht r'), fun hc => hc r hr⟩

/-- Under independence, the truth of a picture is possible but not certain. -/
@[tlp "4.464"]
theorem possibleIn_and_not_certainIn {L : LogicalSpace Atom} (h : Independent L) :
    PossibleIn L p.sense ∧ ¬ CertainIn L p.sense := by
  obtain ⟨⟨r, hr, ht⟩, _⟩ := p.exists_true_and_false h
  exact ⟨⟨r, ht, hr⟩, fun hc => p.not_apriori_true h fun r hr => hc hr⟩

end Picture

/-- The claim that whatever we can describe could also be otherwise: for every picture and
every possible reality, some possible reality gives the picture the opposite
truth-value. -/
@[tlp "5.634"]
def CouldBeOtherwise (L : LogicalSpace Atom) : Prop :=
  ∀ p : Picture Atom, ∀ r ∈ L.possible, ∃ r' ∈ L.possible, (p.IsTrue r ↔ ¬ p.IsTrue r')

/-- Independence implies that whatever can be described could be otherwise. -/
@[tlp "5.634"]
theorem couldBeOtherwise_of_independent {L : LogicalSpace Atom} (h : Independent L) :
    CouldBeOtherwise L := by
  intro p r _
  obtain ⟨⟨rt, hrt, ht⟩, ⟨rf, hrf, hf⟩⟩ := p.exists_true_and_false h
  by_cases hr : p.IsTrue r
  · exact ⟨rf, hrf, ⟨fun _ => hf, fun _ => hr⟩⟩
  · exact ⟨rt, hrt, ⟨fun h' => absurd h' hr, fun h' => absurd ht h'⟩⟩

end Tractatus
