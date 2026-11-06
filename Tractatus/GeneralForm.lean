import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fin.VecNotation
import Mathlib.Logic.Equiv.Fintype
import Tractatus.Consequence

/-!
# The operation N and the general form of proposition (stage 2: 4.5–4.52, 5.234–5.54,
6–6.01)

The syntactic layer (docs/policy.md §3.1): propositional signs are built from elementary
propositions by the operation `N` applied to finitely many signs (6: `[p̄, ξ̄, N(ξ̄)]`), and
are interpreted in the semantic layer of stage 1 (their sense, 4.2).

* `N(ξ̄)` denies all the values of `ξ` (5.502, 5.51),
* truth-operations (5.234) and their compositionality (5.2341, 5.54),
* the main theorem: with finitely many truth-arguments, every truth-function is obtained by
  successive application of `N` to elementary propositions (5.5), and conversely every sign
  built with `N` expresses a truth-function of elementary propositions (5.3, 5.32); so the
  senses of the signs are exactly the truth-functions of elementary propositions (4.5),
* the logical constants are definable from `N` and from one another (5.4, 5.42, 5.474), and
  denial cancels (5.253, 5.254, 5.44).

Only the case where the values of `ξ` are listed one by one (finitely many) is treated; the
values of a function and the terms of a formal series (5.501) need quantification (stage 4a).
-/

namespace Tractatus

variable (Atom : Type*)

/-- Propositional signs in the general form `[p̄, ξ̄, N(ξ̄)]`: an elementary proposition, or
`N` applied to finitely many signs (the values of the variable `ξ`, listed one by one). -/
@[tlp "6", tlp "5.501"]
inductive Formula where
  /-- the elementary proposition of an atomic fact -/
  | elem : Atom → Formula
  /-- `N(ξ̄)` for the listed values `ξ̄` -/
  | N {n : ℕ} : (Fin n → Formula) → Formula

variable {Atom}

/-- `N(ξ̄)`: the negation of all the values of `ξ`, i.e. true exactly where all of them are
false. -/
@[tlp "5.502"]
def NSense {n : ℕ} (ps : Fin n → Sense Atom) : Sense Atom :=
  {r | ∀ i, r ∉ ps i}

/-- With one value, `N(ξ̄) = ~p`; with two values, `N(ξ̄) = ~p . ~q`. -/
@[tlp "5.51"]
theorem NSense_one_two (p q : Sense Atom) : NSense ![p] = pᶜ ∧ NSense ![p, q] = pᶜ ∩ qᶜ := by
  constructor <;> ext r <;> simp [NSense, Fin.forall_fin_two]

namespace Formula

/-- The sense of a propositional sign. -/
def sense : Formula Atom → Sense Atom
  | elem a => elementary a
  | N ps => NSense fun i => (ps i).sense

/-- Denial `~p`, as `N` with one value. -/
def neg (φ : Formula Atom) : Formula Atom := N ![φ]
/-- Logical product `p . q`, as `N(~p, ~q)`. -/
def and (φ ψ : Formula Atom) : Formula Atom := N ![neg φ, neg ψ]
/-- Logical sum `p ∨ q`, as `~N(p, q)`. -/
def or (φ ψ : Formula Atom) : Formula Atom := neg (N ![φ, ψ])
/-- Implication `p ⊃ q`, as `~p ∨ q`. -/
def imp (φ ψ : Formula Atom) : Formula Atom := or (neg φ) ψ

/-- Denial reverses the sense of a proposition. -/
@[tlp "5.2341"]
theorem sense_neg (φ : Formula Atom) : (neg φ).sense = φ.senseᶜ := by
  ext r; simp [neg, sense, NSense]

/-- The logical constants are not further primitive signs or objects: product, sum and
implication are all obtained from `N`, and their senses are the expected ones. -/
@[tlp "5.4"]
theorem sense_and_or_imp (φ ψ : Formula Atom) :
    (and φ ψ).sense = φ.sense ∩ ψ.sense ∧ (or φ ψ).sense = φ.sense ∪ ψ.sense ∧
      (imp φ ψ).sense = φ.senseᶜ ∪ ψ.sense := by
  have hand : (and φ ψ).sense = φ.sense ∩ ψ.sense := by
    ext r; simp [and, sense, NSense, Fin.forall_fin_two, sense_neg]
  have hor : ∀ φ ψ : Formula Atom, (or φ ψ).sense = φ.sense ∪ ψ.sense := by
    intro φ ψ
    ext r
    simp only [or, sense_neg, sense, NSense, Fin.forall_fin_two]
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, Set.mem_union, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    tauto
  exact ⟨hand, hor φ ψ, by rw [imp, hor, sense_neg]⟩

/-- The depth of a sign: how deeply `N` is nested in it. -/
def depth : Formula Atom → ℕ
  | elem _ => 0
  | N ps => (List.ofFn fun i => (ps i).depth).foldr max 0 + 1

theorem depth_neg (φ : Formula Atom) : (neg φ).depth = φ.depth + 1 := by
  simp [neg, depth]

/-- Operations can vanish: `~~p` says the same as `p` (has the same sense), although the sign
`~~p` is a different sign from `p`. Repeated denial does not contain a denial in what it
says; the occurrence of an operation does not characterize the sense. -/
@[tlp "5.254", tlp "5.44", tlp "5.25"]
theorem neg_neg (φ : Formula Atom) : (neg (neg φ)).sense = φ.sense ∧ neg (neg φ) ≠ φ := by
  refine ⟨by rw [sense_neg, sense_neg, compl_compl], fun h => ?_⟩
  have := congrArg depth h
  rw [depth_neg, depth_neg] at this
  omega

/-- The sense of a sign built with `N` depends only on the senses of the signs it is built
from: propositions occur in propositions only as bases of truth-operations, and when the
signs are introduced, the sense of all their combinations is introduced with them. -/
@[tlp "5.2341", tlp "5.54", tlp "5.46"]
theorem sense_N_congr {n : ℕ} {ps qs : Fin n → Formula Atom}
    (h : ∀ i, (ps i).sense = (qs i).sense) : (N ps).sense = (N qs).sense := by
  simp only [sense, h]

end Formula

/-- One operation can reverse the effect of another: denial applied twice cancels. -/
@[tlp "5.253"]
theorem compl_comp_compl : (fun p : Sense Atom => pᶜ) ∘ (fun p => pᶜ) = id := by
  funext p; simp

/-- The logical primitive signs can be defined crosswise: sum from product and denial,
product from sum and denial, implication from product and denial. -/
@[tlp "5.42"]
theorem crosswise_definable (p q : Sense Atom) :
    p ∪ q = (pᶜ ∩ qᶜ)ᶜ ∧ p ∩ q = (pᶜ ∪ qᶜ)ᶜ ∧ pᶜ ∪ q = (p ∩ qᶜ)ᶜ := by
  refine ⟨?_, ?_, ?_⟩ <;> ext r <;>
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff] <;> tauto

/-- The number of fundamental operations depends only on the notation: `N` alone can be
expressed by denial and product (over its values), and denial and product can be expressed by
`N` alone. -/
@[tlp "5.474"]
theorem N_interdefinable {n : ℕ} (ps : Fin n → Sense Atom) (p q : Sense Atom) :
    NSense ps = ⋂ i, (ps i)ᶜ ∧ pᶜ = NSense ![p] ∧ p ∩ q = NSense ![NSense ![p], NSense ![q]] := by
  refine ⟨?_, ?_, ?_⟩ <;> ext r <;> simp [NSense, Fin.forall_fin_two]

/-- There is only one negation of a proposition: a proposition that is false wherever `p` is
true and true wherever `p` is false is exactly `~p`, so any two such propositions are the same.
And `q : p ∨ ~p` says the same as `q`. -/
@[tlp "5.512", tlp "5.513"]
theorem negation_unique (p q s t : Sense Atom) (hs : s ∩ p = ∅ ∧ s ∪ p = Set.univ)
    (ht : t ∩ p = ∅ ∧ t ∪ p = Set.univ) : s = pᶜ ∧ s = t ∧ q ∩ (p ∪ pᶜ) = q := by
  have key : ∀ u : Sense Atom, u ∩ p = ∅ ∧ u ∪ p = Set.univ → u = pᶜ := by
    rintro u ⟨h1, h2⟩
    ext r
    constructor
    · intro hu hp
      have : r ∈ u ∩ p := ⟨hu, hp⟩
      rw [h1] at this
      exact this
    · intro hp
      have : r ∈ u ∪ p := by rw [h2]; exact Set.mem_univ r
      exact this.resolve_right hp
  exact ⟨key s hs, (key s hs).trans (key t ht).symm, by simp⟩

open Classical in
/-- A truth-operation: from the truth-function `f` of `n` places and `n` propositions as
bases, the proposition true exactly where `f` is true at the row of the bases' truth-values. -/
@[tlp "5.234"]
noncomputable def truthOp {n : ℕ} (f : TruthFunction n) (ps : Fin n → Sense Atom) : Sense Atom :=
  {r | f (fun i => decide (r ∈ ps i)) = true}

/-- A truth-operation applied to elementary propositions gives the truth-function of them. -/
@[tlp "5.234"]
theorem truthOp_elementary {n : ℕ} (f : TruthFunction n) (args : Fin n → Atom) :
    truthOp f (fun i => elementary (args i)) = applyTF f args := by
  classical
  ext r
  have : (fun i => decide (r ∈ elementary (args i))) = fun i => r (args i) := by
    funext i
    cases h : r (args i) <;> simp [elementary, h]
  simp only [truthOp, Set.mem_ofPred_eq, applyTF]
  rw [this]

/-- A truth-function whose truth-arguments are indexed by any finite type is a truth-function
of elementary propositions. -/
theorem isTruthFunction_of_fintype {ι : Type*} [Fintype ι] (g : (ι → Bool) → Bool)
    (args : ι → Atom) : IsTruthFunctionOfElementary {r | g (fun i => r (args i)) = true} := by
  classical
  let e := Fintype.equivFin ι
  refine ⟨Fintype.card ι, fun w => g (fun i => w (e i)), fun j => args (e.symm j), ?_⟩
  ext r
  simp [applyTF]

/-- The schemata of 4.31 also make sense when `p, q, r, …` are not elementary propositions:
a truth-operation applied to truth-functions of elementary propositions gives again a
truth-function of elementary propositions. -/
@[tlp "5.31"]
theorem isTruthFunction_truthOp {n : ℕ} (f : TruthFunction n) {ps : Fin n → Sense Atom}
    (h : ∀ i, IsTruthFunctionOfElementary (ps i)) :
    IsTruthFunctionOfElementary (truthOp f ps) := by
  classical
  choose m g args hps using h
  have := isTruthFunction_of_fintype (ι := Σ i, Fin (m i))
    (fun w => f (fun i => g i (fun j => w ⟨i, j⟩))) (fun x => args x.1 x.2)
  convert this using 1
  ext r
  simp [truthOp, hps, applyTF]

/-- Every sign built with `N` expresses a truth-function of (finitely many) elementary
propositions: all propositions so built are results of truth-operations on elementary
propositions, after finitely many steps. -/
@[tlp "5.3", tlp "5.32"]
theorem Formula.isTruthFunction (φ : Formula Atom) : IsTruthFunctionOfElementary φ.sense := by
  classical
  induction φ with
  | elem a => exact elementary_isTruthFunction a
  | N ps ih =>
    have : (Formula.N ps).sense = truthOp (fun v => decide (∀ i, v i = false))
        (fun i => (ps i).sense) := by
      ext r
      simp [Formula.sense, NSense, truthOp]
    rw [this]
    exact isTruthFunction_truthOp _ ih

namespace Formula

/-- The sign that is true exactly at the row `v` of the truth-values of `args`: `N` of the
denials of the literals of `v`. -/
def rowSign {n : ℕ} (args : Fin n → Atom) (v : Fin n → Bool) : Formula Atom :=
  N fun i => if v i then neg (elem (args i)) else elem (args i)

theorem mem_rowSign_iff {n : ℕ} (args : Fin n → Atom) (v : Fin n → Bool) (r : Reality Atom) :
    r ∈ (rowSign args v).sense ↔ (fun i => r (args i)) = v := by
  simp only [rowSign, sense, NSense, Set.mem_ofPred_eq, funext_iff]
  refine forall_congr' fun i => ?_
  cases hv : v i <;> simp [sense_neg, sense, elementary]

end Formula

/-- Every truth-function of finitely many elementary propositions is the sense of a sign
built by successive application of `N` to elementary propositions; `N` is the one general
primitive sign. -/
@[tlp "5.5", tlp "5.472"]
theorem exists_formula_of_truthFunction {n : ℕ} (f : TruthFunction n) (args : Fin n → Atom) :
    ∃ φ : Formula Atom, φ.sense = applyTF f args := by
  classical
  let T := {v : Fin n → Bool // f v = true}
  let e := Fintype.equivFin T
  refine ⟨Formula.neg (Formula.N fun j => Formula.rowSign args (e.symm j).1), ?_⟩
  ext r
  simp only [Formula.sense_neg, Formula.sense, NSense, Set.mem_compl_iff, Set.mem_ofPred_eq,
    Formula.mem_rowSign_iff, not_forall, not_not, applyTF]
  constructor
  · rintro ⟨j, hj⟩
    rw [hj]
    exact (e.symm j).2
  · intro hf
    exact ⟨e ⟨_, hf⟩, by simp⟩

/-- The most general form of proposition can be given: the senses of the signs built with `N`
are exactly the truth-functions of elementary propositions. -/
@[tlp "4.5", tlp "5.5"]
theorem range_sense :
    Set.range (Formula.sense (Atom := Atom)) = {p | IsTruthFunctionOfElementary p} := by
  ext p
  constructor
  · rintro ⟨φ, rfl⟩
    exact φ.isTruthFunction
  · rintro ⟨n, f, args, rfl⟩
    exact exists_formula_of_truthFunction f args

/-- Results of truth-operations that are the same truth-function of elementary propositions
are identical (have the same sense). -/
@[tlp "5.41"]
theorem sense_eq_of_same_truthFunction {φ ψ : Formula Atom} {n : ℕ} {f : TruthFunction n}
    {args : Fin n → Atom} (hφ : φ.sense = applyTF f args) (hψ : ψ.sense = applyTF f args) :
    φ.sense = ψ.sense :=
  hφ.trans hψ.symm

/-- The claim that all propositions of a language are results of truth-operations on
elementary propositions, i.e. have the sense of a sign of the general form. If all
elementary propositions are given, the propositions are what can be built from them. -/
@[tlp "5.3", tlp "5.32", tlp "6.001", tlp "4.51", tlp "4.52"]
def GeneralFormThesis (P : Language Atom) : Prop :=
  ∀ p ∈ P, ∃ φ : Formula Atom, φ.sense = p

/-- The claim of 6.001 (every proposition is the result of successive applications of `N` to
elementary propositions) is equivalent to the claim of 5 (every proposition is a
truth-function of elementary propositions). -/
@[tlp "6.001", tlp "5.3"]
theorem generalFormThesis_iff_extensionalityThesis (P : Language Atom) :
    GeneralFormThesis P ↔ ExtensionalityThesis P := by
  constructor
  · intro h p hp
    obtain ⟨φ, rfl⟩ := h p hp
    exact φ.isTruthFunction
  · intro h p hp
    obtain ⟨n, f, args, rfl⟩ := h p hp
    exact exists_formula_of_truthFunction f args

/-- The general form of an operation `[η̄, ξ̄, N(ξ̄)]`: the propositions obtained from the bases
`η̄` (the set `B`) by successive application of `N` to finitely many propositions already
obtained. -/
@[tlp "6.01"]
inductive Generated (B : Set (Sense Atom)) : Sense Atom → Prop
  | base {p : Sense Atom} : p ∈ B → Generated B p
  | N {n : ℕ} (ps : Fin n → Sense Atom) : (∀ i, Generated B (ps i)) → Generated B (NSense ps)

/-- Given the general form of the construction of propositions, the general form of the
operation is given too: the general form of proposition is that operation applied to the
elementary propositions. -/
@[tlp "6.002"]
theorem generated_elementary_eq_range :
    {p | Generated (Set.range (elementary (Atom := Atom))) p} = Set.range Formula.sense := by
  ext p
  constructor
  · intro h
    induction h with
    | base hp =>
      obtain ⟨a, rfl⟩ := hp
      exact ⟨Formula.elem a, rfl⟩
    | N ps _ ih =>
      choose φ hφ using ih
      exact ⟨Formula.N φ, by simp only [Formula.sense, hφ]⟩
  · rintro ⟨φ, rfl⟩
    induction φ with
    | elem a => exact Generated.base ⟨a, rfl⟩
    | N ps ih => exact Generated.N _ ih

open Classical in
/-- If a proposition is given, the results of all truth-operations having it as their only
base are given with it: there are exactly four, the contradiction, the proposition itself, its
denial and the tautology. -/
@[tlp "5.442"]
theorem truthOp_one_mem (f : TruthFunction 1) (p : Sense Atom) :
    truthOp f ![p] ∈ ({∅, p, pᶜ, Set.univ} : Set (Sense Atom)) := by
  have key : ∀ r : Reality Atom, (fun i => decide (r ∈ (![p] : Fin 1 → Sense Atom) i)) =
      if r ∈ p then ![true] else ![false] := by
    intro r
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    by_cases hr : r ∈ p <;> simp [hr]
  have ht : ∀ r, r ∈ truthOp f ![p] ↔ f (if r ∈ p then ![true] else ![false]) = true := by
    intro r
    simp only [truthOp, Set.mem_ofPred_eq, key]
  cases h1 : f ![true] <;> cases h0 : f ![false]
  · left; ext r; by_cases hr : r ∈ p <;> simp [ht, hr, h1, h0]
  · right; right; left; ext r; by_cases hr : r ∈ p <;> simp [ht, hr, h1, h0]
  · right; left; ext r; by_cases hr : r ∈ p <;> simp [ht, hr, h1, h0]
  · right; right; right; ext r; by_cases hr : r ∈ p <;> simp [ht, hr, h1, h0]

end Tractatus
