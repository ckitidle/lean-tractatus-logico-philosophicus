import Tractatus.GeneralForm

/-!
# The propositions of logic (stage 2: 5.43, 6.1–6.127, 6.37, 6.375)

A proposition of logic is defined as a sign whose sense is a tautology (6.1;
analysis/interpretation.md, logic_tautology). No proof system is set up.

* propositions of logic say nothing (6.11) and are all the same (5.43, 6.127),
* whether a sign is a tautology can be computed from the sign alone (6.113, 6.125, 6.1203),
  and so can consequence (6.122),
* the "zero method": a tautology of the right shape shows a logical relation, e.g.
  contradiction or consequence (6.1201, 6.121, 6.1221), and contradictions would do as well
  (6.1202); modus ponens (6.1264),
* only tautologies follow from tautologies (6.126), and they cannot be confirmed or refuted
  by experience (6.1222),
* the claims that the only necessity and impossibility are logical ones (6.37, 6.375).
-/

namespace Tractatus

variable {Atom : Type*}

/-- A proposition of logic: a sign whose sense is a tautology. -/
@[tlp "6.1"]
def IsLogicalProposition (φ : Formula Atom) : Prop :=
  IsTautology φ.sense

/-- The propositions of logic say nothing: they are without sense, and exclude no possible
reality. -/
@[tlp "6.11"]
theorem IsLogicalProposition.saysNothing {φ : Formula Atom} (h : IsLogicalProposition φ)
    (L : LogicalSpace Atom) : Senseless φ.sense ∧ content L φ.sense = ∅ :=
  ⟨Or.inl h, (tautology_follows h φ.sense (L := L)).2⟩

/-- All tautologies are one and the same proposition; so all propositions of logic say the
same, namely nothing, and none of them is more primitive than another. -/
@[tlp "5.43", tlp "6.127"]
theorem eq_of_tautology {p q : Sense Atom} (hp : IsTautology p) (hq : IsTautology q) : p = q := by
  ext r
  exact ⟨fun _ => hq r, fun _ => hp r⟩

/-- From `p` follow `~~p`, `~~~~p`, …, but they are all the same proposition as `p`. -/
@[tlp "5.43"]
theorem iterate_double_neg (p : Sense Atom) (n : ℕ) : (fun q : Sense Atom => qᶜᶜ)^[n] p = p := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, compl_compl]

namespace Formula

/-- The truth-value of a sign at a truth-possibility, computed from the sign. -/
def eval (r : Reality Atom) : Formula Atom → Bool
  | elem a => r a
  | N ps => decide (∀ i, (ps i).eval r = false)

theorem mem_sense_iff_eval (φ : Formula Atom) (r : Reality Atom) :
    r ∈ φ.sense ↔ φ.eval r = true := by
  induction φ with
  | elem a => rfl
  | N ps ih =>
    simp only [sense, NSense, Set.mem_ofPred_eq, eval, decide_eq_true_eq]
    exact forall_congr' fun i => by rw [ih i]; simp

end Formula

/-- The method of recognizing a tautology from the sign (for signs without generality, with
finitely many atomic facts): compute the truth-value of the sign at every row and check that
it is always true. -/
@[tlp "6.1203"]
def isTautologyB [Fintype Atom] [DecidableEq Atom] (φ : Formula Atom) : Bool :=
  decide (∀ r : Reality Atom, φ.eval r = true)

/-- One can perceive from the sign alone that a proposition of logic is true: the computation
decides it. All the propositions of logic can be described at the outset, and there can be no
surprises in logic. -/
@[tlp "6.113", tlp "6.125", tlp "6.1251", tlp "6.1203"]
theorem isTautologyB_iff [Fintype Atom] [DecidableEq Atom] (φ : Formula Atom) :
    isTautologyB φ = true ↔ IsLogicalProposition φ := by
  simp only [isTautologyB, decide_eq_true_eq, IsLogicalProposition, IsTautology,
    Formula.mem_sense_iff_eval]

/-- For example, `p ∨ ~p` is recognized as a proposition of logic, and `p` is not. -/
@[tlp "6.113"]
theorem isTautologyB_examples :
    isTautologyB (Formula.or (Formula.elem 0) (Formula.neg (Formula.elem 0)) : Formula (Fin 1))
      = true ∧ isTautologyB (Formula.elem 0 : Formula (Fin 1)) = false := by
  decide

/-- A proposition that is not a proposition of logic (nor a contradiction) can be true and
can be false: its truth cannot be seen from the sign alone. -/
@[tlp "6.113"]
theorem exists_true_false_of_not_senseless {p : Sense Atom} (h : ¬ Senseless p) :
    (∃ r, r ∈ p) ∧ ∃ r, r ∉ p := by
  simp only [Senseless, IsTautology, IsContradiction, not_or, not_forall, not_not] at h
  exact ⟨h.2, h.1⟩

/-- Consequence can be recognized from the signs alone, without forming a proposition of
logic: under independence it comes down to computing the two signs at every row (a finite
check when there are finitely many atomic facts). -/
@[tlp "6.122"]
theorem follows_iff_eval {L : LogicalSpace Atom} (h : Independent L)
    (φ ψ : Formula Atom) :
    Follows L φ.sense ψ.sense ↔ ∀ r : Reality Atom, ψ.eval r = true → φ.eval r = true := by
  have h' : L.possible = Set.univ := h
  simp only [Follows, h', Set.inter_univ, Set.subset_def, Formula.mem_sense_iff_eval]

/-- `p` and `~p` give a tautology in `~(p . ~p)`; in general two propositions contradict
each other exactly when the denial of their product is a tautology. And modus ponens: from
`p ⊃ q` and `p`, `q`: the sign `(p ⊃ q) . p : ⊃ : q` is a tautology. -/
@[tlp "6.1201", tlp "6.121", tlp "6.1264"]
theorem tautology_shows (p q : Sense Atom) :
    IsTautology (p ∩ pᶜ)ᶜ ∧ (IsTautology (p ∩ q)ᶜ ↔ p ∩ q = ∅) ∧
      IsTautology (((pᶜ ∪ q) ∩ p)ᶜ ∪ q) := by
  refine ⟨fun r hr => hr.2 hr.1, ⟨fun h => ?_, fun h r hr => ?_⟩, fun r => ?_⟩
  · exact Set.eq_empty_iff_forall_notMem.mpr fun r hr => h r hr
  · rw [h] at hr; exact hr
  · by_cases hq : r ∈ q
    · exact Or.inr hq
    · refine Or.inl fun ⟨hpq, hp⟩ => ?_
      rcases hpq with hnp | hq'
      · exact hnp hp
      · exact hq hq'

/-- Under independence, `q` follows from `p` exactly when `p ⊃ q` is a tautology. -/
@[tlp "6.1221", tlp "6.1201"]
theorem tautology_imp_iff_follows {L : LogicalSpace Atom} (h : Independent L)
    (p q : Sense Atom) : IsTautology (pᶜ ∪ q) ↔ Follows L q p := by
  have hu : ∀ r, r ∈ L.possible := fun r => by rw [h]; exact Set.mem_univ _
  constructor
  · intro ht r ⟨hp, _⟩
    rcases ht r with hnp | hq
    · exact absurd hp hnp
    · exact hq
  · intro hf r
    by_cases hp : r ∈ p
    · exact Or.inr (hf ⟨hp, hu r⟩)
    · exact Or.inl hp

/-- Contradictions would serve as well: under independence, `q` follows from `p` exactly when
`p . ~q` is a contradiction. -/
@[tlp "6.1202"]
theorem contradiction_iff_follows {L : LogicalSpace Atom} (h : Independent L)
    (p q : Sense Atom) : IsContradiction (p ∩ qᶜ) ↔ Follows L q p := by
  have hu : ∀ r, r ∈ L.possible := fun r => by rw [h]; exact Set.mem_univ _
  constructor
  · intro hc r ⟨hp, _⟩
    by_contra hq
    exact hc r ⟨hp, hq⟩
  · intro hf r ⟨hp, hq⟩
    exact hq (hf ⟨hp, hu r⟩)

/-- Under independence, only tautologies follow from a tautology: transforming propositions
of logic by valid steps gives propositions of logic. -/
@[tlp "6.126"]
theorem tautology_of_follows {L : LogicalSpace Atom} (h : Independent L) {p q : Sense Atom}
    (hp : IsTautology p) (hf : Follows L q p) : IsTautology q := by
  intro r
  exact hf ⟨hp r, by rw [h]; exact Set.mem_univ _⟩

/-- A proposition of logic can neither be confirmed nor refuted by experience: it is true in
every possible reality of every logical space, so no possible reality refutes it, and its truth
is certain whatever the logical space. -/
@[tlp "6.1222"]
theorem tautology_not_empirical {p : Sense Atom} (hp : IsTautology p) (L : LogicalSpace Atom) :
    CertainIn L p ∧ ¬ ∃ r ∈ L.possible, r ∉ p :=
  ⟨certainIn_of_tautology hp L, fun ⟨r, _, hr⟩ => hr (hp r)⟩

/-- Signs that serve one purpose (have the same sense) are logically equivalent: their
biconditional `(p ⊃ q) . (q ⊃ p)` is a proposition of logic. -/
@[tlp "5.47321"]
theorem logically_equivalent_of_sense_eq {φ ψ : Formula Atom} (h : φ.sense = ψ.sense) :
    IsLogicalProposition (Formula.and (Formula.imp φ ψ) (Formula.imp ψ φ)) := by
  intro r
  obtain ⟨hand, -, -⟩ := Formula.sense_and_or_imp (Formula.imp φ ψ) (Formula.imp ψ φ)
  obtain ⟨-, -, himp1⟩ := Formula.sense_and_or_imp φ ψ
  obtain ⟨-, -, himp2⟩ := Formula.sense_and_or_imp ψ φ
  rw [hand, himp1, himp2, h]
  by_cases hr : r ∈ ψ.sense
  · exact ⟨Or.inr hr, Or.inr hr⟩
  · exact ⟨Or.inl hr, Or.inl hr⟩

/-- The claim that there is only logical necessity: whatever is certain in the logical space
is a tautology. -/
@[tlp "6.37"]
def OnlyLogicalNecessity (L : LogicalSpace Atom) : Prop :=
  ∀ p : Sense Atom, CertainIn L p → IsTautology p

/-- The claim that there is only logical impossibility: whatever is impossible in the logical
space is a contradiction. -/
@[tlp "6.375"]
def OnlyLogicalImpossibility (L : LogicalSpace Atom) : Prop :=
  ∀ p : Sense Atom, ImpossibleIn L p → IsContradiction p

/-- Independence implies that there is only logical necessity. -/
@[tlp "6.37"]
theorem onlyLogicalNecessity_of_independent {L : LogicalSpace Atom} (h : Independent L) :
    OnlyLogicalNecessity L := by
  intro p hc r
  exact hc (by rw [h]; exact Set.mem_univ r)

/-- Independence implies that there is only logical impossibility. -/
@[tlp "6.375"]
theorem onlyLogicalImpossibility_of_independent {L : LogicalSpace Atom} (h : Independent L) :
    OnlyLogicalImpossibility L := by
  intro p hi r hr
  have : r ∈ p ∩ L.possible := ⟨hr, by rw [h]; exact Set.mem_univ r⟩
  rw [hi] at this
  exact this

end Tractatus
