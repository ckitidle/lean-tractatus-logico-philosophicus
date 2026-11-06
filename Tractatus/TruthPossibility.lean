import Mathlib.Data.Nat.Choose.Sum
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Fintype.Pi
import Mathlib.Logic.Equiv.Fintype
import Tractatus.LogicalSpace

/-!
# Truth-possibilities, sense, tautology and truth-functions (stage 1)

* the sense of a proposition is represented by the set of truth-possibilities it agrees
  with (4.2),
* counting truth-possibilities and truth-functions (4.27, 4.42, 5.101),
* tautology and contradiction (4.46) and what they say (4.461–4.465),
* elementary propositions (4.21–4.28), the schema of truth-possibilities (4.31) and the
  notation `(TTFT)(p, q)` (4.43–4.442),
* propositions as truth-functions of elementary propositions (4.4, 4.41, 5, 5.01).
-/

namespace Tractatus

/-- The sense of a proposition, represented by the set of realities (truth-possibilities)
with which it agrees; it disagrees with the rest. -/
@[tlp "4.2"]
abbrev Sense (Atom : Type*) := Set (Reality Atom)

/-- The truth-possibilities of the elementary propositions are the possibilities of the
existence and non-existence of the atomic facts: the same assignments as realities. -/
@[tlp "4.3"]
abbrev TruthPossibility (Atom : Type*) := Reality Atom

/-- A language, as a totality of propositions (given by their senses). -/
@[tlp "4.001"]
abbrev Language (Atom : Type*) := Set (Sense Atom)

variable {Atom : Type*}

/-- Under independence, a finite number `n` of atomic facts gives
`K_n = ∑_{ν=0}^{n} (n choose ν)` possible realities (which equals `2 ^ n`), since every
combination is possible. -/
@[tlp "4.27"]
theorem card_possible_of_independent [Finite Atom] {L : LogicalSpace Atom}
    (h : Independent L) :
    Nat.card L.possible = ∑ ν ∈ Finset.range (Nat.card Atom + 1), (Nat.card Atom).choose ν := by
  rw [Nat.sum_range_choose, h, Nat.card_univ, Nat.card_fun]
  simp

/-- A proposition (given by its sense) is a tautology if it is true for every
truth-possibility. -/
@[tlp "4.46"]
def IsTautology (p : Sense Atom) : Prop :=
  ∀ r, r ∈ p

/-- A proposition (given by its sense) is a contradiction if it is false for every
truth-possibility. -/
@[tlp "4.46"]
def IsContradiction (p : Sense Atom) : Prop :=
  ∀ r, r ∉ p

/-- A truth-function of `n` elementary propositions, in the manner of the schema of 5.101:
it assigns true or false to each row, i.e. to each truth-possibility of the `n`
arguments. -/
@[tlp "5.101", tlp "4.4"]
abbrev TruthFunction (n : ℕ) := (Fin n → Bool) → Bool

/-- The truth-grounds of a truth-function: the rows (truth-possibilities of the
arguments) at which it is true. -/
@[tlp "5.101"]
def truthGrounds {n : ℕ} (f : TruthFunction n) : Set (Fin n → Bool) :=
  {r | f r = true}

/-- The number of truth-functions of `n` elementary propositions is
`L_n = ∑_{κ=0}^{K_n} (K_n choose κ)` with `K_n = 2 ^ n` (so `L_n = 2 ^ (2 ^ n)`): a
truth-function is fixed by the set of rows at which it is true. -/
@[tlp "4.42"]
theorem card_truthFunction (n : ℕ) :
    Nat.card (TruthFunction n) = ∑ κ ∈ Finset.range (2 ^ n + 1), (2 ^ n).choose κ := by
  rw [Nat.sum_range_choose]
  simp [TruthFunction]

/-- There are exactly 16 truth-functions of two elementary propositions: the 16 rows of
the schema in 5.101. -/
@[tlp "5.101"]
theorem card_truthFunction_two : Nat.card (TruthFunction 2) = 16 := by
  rw [card_truthFunction, Nat.sum_range_choose]
  norm_num

/-! ## Elementary propositions (4.21–4.28) -/

/-- The elementary proposition asserting the existence of the atomic fact `a`: it is true
exactly at the truth-possibilities where `a` obtains. -/
@[tlp "4.21"]
def elementary (a : Atom) : Sense Atom :=
  {r | r a = true}

/-- An elementary proposition is true exactly when its atomic fact exists, and false exactly
when it does not. -/
@[tlp "4.25"]
theorem mem_elementary_iff {a : Atom} {r : Reality Atom} :
    (r ∈ elementary a ↔ r a = true) ∧ (r ∉ elementary a ↔ r a = false) := by
  simp [elementary]

/-- Which elementary propositions are true settles the whole of reality: two realities that
make the same elementary propositions true are the same. -/
@[tlp "4.26"]
theorem reality_eq_iff_elementary {r r' : Reality Atom} :
    r = r' ↔ ∀ a, (r ∈ elementary a ↔ r' ∈ elementary a) := by
  constructor
  · rintro rfl _
    rfl
  · intro h
    funext a
    have := h a
    simp only [elementary, Set.mem_ofPred_eq] at this
    cases hr : r a <;> cases hr' : r' a <;> simp_all

/-- The claim that no elementary proposition contradicts another: any two elementary
propositions can be true together in some possible reality. -/
@[tlp "4.211"]
def ElementaryCompatible (L : LogicalSpace Atom) : Prop :=
  ∀ a b : Atom, (elementary a ∩ elementary b ∩ L.possible).Nonempty

/-- Independence (2.061) implies that elementary propositions do not contradict each
other. -/
@[tlp "4.211"]
theorem elementaryCompatible_of_independent {L : LogicalSpace Atom} (h : Independent L) :
    ElementaryCompatible L := by
  intro a b
  refine ⟨fun _ => true, ⟨rfl, rfl⟩, ?_⟩
  rw [h]
  exact Set.mem_univ _

/-- The truth-possibilities of `n` elementary propositions are as many as the combinations of
`n` atomic facts: `K_n = ∑_{ν=0}^{n} (n choose ν)`. -/
@[tlp "4.28"]
theorem card_truthPossibilities (n : ℕ) :
    Nat.card (Fin n → Bool) = ∑ ν ∈ Finset.range (n + 1), n.choose ν := by
  rw [Nat.sum_range_choose]
  simp

/-- Under independence, the possible realities of finitely many atomic facts are exactly as
many as the truth-possibilities of the same number of elementary propositions. -/
@[tlp "4.28"]
theorem card_possible_eq_card_truthPossibilities [Finite Atom] {L : LogicalSpace Atom}
    (h : Independent L) : Nat.card L.possible = Nat.card (Fin (Nat.card Atom) → Bool) := by
  rw [card_possible_of_independent h, card_truthPossibilities]

/-! ## The schema of truth-possibilities and the notation `(TTFT)(p, q)` (4.31–4.45) -/

/-- The rows of the schema of truth-possibilities of `n` elementary propositions, in the order
used in the *Tractatus*: first the row without `F`, then the rows with one `F` (at the first
place, the second place, …), then those with two, and so on. Row `v` gives the truth-value
`v i` of the `i`-th elementary proposition. -/
@[tlp "4.31"]
def truthTable (n : ℕ) : List (Fin n → Bool) :=
  ((List.range (n + 1)).flatMap fun k =>
      (List.finRange n).sublists.filter (·.length == k)).map
    fun S i => decide (i ∉ S)

/-- Every truth-possibility of `n` elementary propositions is a row of the schema. -/
@[tlp "4.31"]
theorem mem_truthTable {n : ℕ} (v : Fin n → Bool) : v ∈ truthTable n := by
  let S := (List.finRange n).filter (fun i => v i == false)
  have hS : S.Sublist (List.finRange n) := List.filter_sublist
  simp only [truthTable, List.mem_map, List.mem_flatMap, List.mem_range, List.mem_filter,
    List.mem_sublists, beq_iff_eq]
  refine ⟨S, ⟨S.length, ?_, hS, rfl⟩, ?_⟩
  · have := hS.length_le
    simp only [List.length_finRange] at this
    omega
  · funext i
    cases hv : v i <;> simp [S, hv]

/-- The schema for three elementary propositions `p, q, r` has the rows of 4.31, in the same
order (`true` for T, `false` for F). -/
@[tlp "4.31"]
theorem truthTable_three :
    (truthTable 3).map List.ofFn =
      [[true, true, true], [false, true, true], [true, false, true], [true, true, false],
        [false, false, true], [false, true, false], [true, false, false],
        [false, false, false]] := by
  decide

/-- The schema for two elementary propositions `p, q`: rows TT, FT, TF, FF. -/
@[tlp "4.31"]
theorem truthTable_two :
    (truthTable 2).map List.ofFn =
      [[true, true], [false, true], [true, false], [false, false]] := by
  decide

/-- The column of marks of a truth-function: for each row of the schema, in order, whether
the proposition agrees (`true`, the mark T) or not. -/
@[tlp "4.43"]
def column {n : ℕ} (f : TruthFunction n) : List Bool :=
  (truthTable n).map f

/-- The notation `(TTFT)(p, q)`: the truth-function given by a column of marks, read against
the rows of the schema in their fixed order. -/
@[tlp "4.442"]
def ofColumn {n : ℕ} (col : List Bool) : TruthFunction n :=
  fun v => col.getD ((truthTable n).idxOf v) false

/-- The sign obtained by coordinating the marks with the truth-possibilities expresses the
proposition completely: reading back the column of a truth-function gives the same
truth-function. -/
@[tlp "4.44"]
theorem ofColumn_column {n : ℕ} (f : TruthFunction n) : ofColumn (column f) = f := by
  funext v
  have hv : (truthTable n).idxOf v < (truthTable n).length :=
    List.idxOf_lt_length_iff.mpr (mem_truthTable v)
  simp only [ofColumn, column]
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hv]
  simp [List.getElem_idxOf]

/-- `(TTFT)(p, q)` is "if p then q" (4.442, and the corresponding row of 5.101). -/
@[tlp "4.442"]
theorem ofColumn_TTFT : (ofColumn [true, true, false, true] : TruthFunction 2) =
    fun v => !v 0 || v 1 := by
  decide

/-- The truth-functions of `n` elementary propositions (the `L_n` groups of truth-conditions)
can be ordered in a series: they can be numbered `0, 1, …, L_n - 1`. -/
@[tlp "4.45", tlp "5.1"]
theorem truthFunctions_in_series (n : ℕ) : Nonempty (TruthFunction n ≃ Fin (2 ^ 2 ^ n)) :=
  ⟨Fintype.equivFinOfCardEq (by simp [TruthFunction])⟩

/-! ## Propositions as truth-functions of elementary propositions (4.4, 4.41, 5, 5.01) -/

/-- The proposition obtained from the truth-function `f` with the elementary propositions of
the atomic facts `args i` as its truth-arguments: it is true at a truth-possibility when `f`
is true at the row of the arguments' truth-values. -/
@[tlp "5.01"]
def applyTF {n : ℕ} (f : TruthFunction n) (args : Fin n → Atom) : Sense Atom :=
  {r | f (fun i => r (args i)) = true}

/-- The truth-possibilities of the elementary propositions are the conditions of truth and
falsehood of a proposition: its truth-value depends only on the truth-values of its
truth-arguments. -/
@[tlp "4.41"]
theorem mem_applyTF_congr {n : ℕ} {f : TruthFunction n} {args : Fin n → Atom}
    {r r' : Reality Atom} (h : ∀ i, r (args i) = r' (args i)) :
    r ∈ applyTF f args ↔ r' ∈ applyTF f args := by
  simp only [applyTF, Set.mem_ofPred_eq, h]

/-- A sense is a truth-function of (finitely many) elementary propositions. -/
def IsTruthFunctionOfElementary (p : Sense Atom) : Prop :=
  ∃ n, ∃ f : TruthFunction n, ∃ args : Fin n → Atom, p = applyTF f args

/-- The claim that every proposition of a language is a truth-function of elementary
propositions. -/
@[tlp "5"]
def ExtensionalityThesis (P : Language Atom) : Prop :=
  ∀ p ∈ P, IsTruthFunctionOfElementary p

/-- An elementary proposition is a truth-function of itself. -/
@[tlp "5"]
theorem elementary_isTruthFunction (a : Atom) :
    IsTruthFunctionOfElementary (elementary a) :=
  ⟨1, fun v => v 0, fun _ => a, rfl⟩

/-! ## What tautology and contradiction say (4.461–4.465) -/

/-- Being without sense (*sinnlos*): being a tautology or a contradiction. -/
@[tlp "4.461"]
def Senseless (p : Sense Atom) : Prop :=
  IsTautology p ∨ IsContradiction p

/-- Tautology and contradiction say nothing: a proposition is without sense exactly when its
truth does not depend on the truth-possibility at all (it has no truth-conditions). -/
@[tlp "4.461"]
theorem senseless_iff_unconditional (p : Sense Atom) :
    Senseless p ↔ ∀ r r', (r ∈ p ↔ r' ∈ p) := by
  constructor
  · rintro (h | h) r r'
    · exact ⟨fun _ => h r', fun _ => h r⟩
    · exact ⟨fun hr => absurd hr (h r), fun hr => absurd hr (h r')⟩
  · intro h
    by_cases h0 : (fun _ => true) ∈ p
    · exact Or.inl fun r => (h r _).mpr h0
    · exact Or.inr fun r hr => h0 ((h r _).mp hr)

/-- Tautology and contradiction are still part of the symbolism: they are truth-functions of
elementary propositions (with no arguments), like `0` in arithmetic. -/
@[tlp "4.4611"]
theorem isTruthFunction_of_senseless {p : Sense Atom} (h : Senseless p) :
    IsTruthFunctionOfElementary p := by
  rcases h with h | h
  · refine ⟨0, fun _ => true, Fin.elim0, ?_⟩
    ext r
    simp [applyTF, h r]
  · refine ⟨0, fun _ => false, Fin.elim0, ?_⟩
    ext r
    simp [applyTF, h r]

/-- The truth-conditions fix the range a proposition leaves to the facts within a logical
space: a tautology leaves the whole logical space, a contradiction leaves nothing. -/
@[tlp "4.463"]
theorem inter_possible_of_tautology {p : Sense Atom} (h : IsTautology p) (L : LogicalSpace Atom) :
    p ∩ L.possible = L.possible :=
  Set.inter_eq_right.mpr fun r _ => h r

@[tlp "4.463"]
theorem inter_possible_of_contradiction {p : Sense Atom} (h : IsContradiction p)
    (L : LogicalSpace Atom) : p ∩ L.possible = ∅ :=
  Set.eq_empty_iff_forall_notMem.mpr fun r hr => h r hr.1

/-- The truth of a proposition is certain in a logical space if it holds at every possible
reality. -/
@[tlp "4.464"]
def CertainIn (L : LogicalSpace Atom) (p : Sense Atom) : Prop :=
  L.possible ⊆ p

/-- The truth of a proposition is possible in a logical space if it holds at some possible
reality. -/
@[tlp "4.464"]
def PossibleIn (L : LogicalSpace Atom) (p : Sense Atom) : Prop :=
  (p ∩ L.possible).Nonempty

/-- The truth of a proposition is impossible in a logical space if it holds at no possible
reality. -/
@[tlp "4.464"]
def ImpossibleIn (L : LogicalSpace Atom) (p : Sense Atom) : Prop :=
  p ∩ L.possible = ∅

/-- The truth of a tautology is certain. -/
@[tlp "4.464"]
theorem certainIn_of_tautology {p : Sense Atom} (h : IsTautology p) (L : LogicalSpace Atom) :
    CertainIn L p :=
  fun r _ => h r

/-- The truth of a contradiction is impossible. -/
@[tlp "4.464"]
theorem impossibleIn_of_contradiction {p : Sense Atom} (h : IsContradiction p)
    (L : LogicalSpace Atom) : ImpossibleIn L p :=
  inter_possible_of_contradiction h L

/-- The logical product of a tautology and a proposition is the proposition itself. -/
@[tlp "4.465"]
theorem inter_of_tautology {t : Sense Atom} (h : IsTautology t) (p : Sense Atom) : t ∩ p = p :=
  Set.inter_eq_right.mpr fun r _ => h r

end Tractatus
