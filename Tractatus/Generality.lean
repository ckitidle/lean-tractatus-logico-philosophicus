import Mathlib.Logic.Function.Basic
import Tractatus.Names

/-!
# Generality over finitely many objects (stage 4a: 5.441, 5.52–5.525, 6.1231)

A language with quantifiers over names: elementary sentences whose places may be filled by
variables, `N` applied to finitely many signs, and the quantifiers `(∃x)` and `(x)`. The
quantifiers range over all objects (the type of objects is the range of the variables, 5.523,
5.524).

* The main theorem (5.52): when finitely many names name every object, a quantified sign
  translates into a sign built from elementary sentences with `N` alone, with the same sense.
  `(∃x) . fx` becomes `~N(fa, fb, …)`, `N` of all the values of `fx` denied, and `(x) . fx`
  becomes `N(~fa, ~fb, …)`.
* The concept "all" is separated from the truth-function: the sense depends only on the values
  of the function, not on how they are listed (5.521).
* `~(∃x) . ~fx` and `(x) . fx` say the same (5.441).
* `(∃x) . fx` is not the proposition "`fx` is possible" (5.525), and a proposition can be true
  of every object without being a tautology, while a proposition without generality can be a
  tautology (6.1231).

Only finitely many objects are treated: with infinitely many, the translation would need `N`
applied to infinitely many signs. The variables are read inclusively (two variables may take
the same object); the exclusive reading of 5.532 is deferred (stage 4c).
-/

namespace Tractatus

variable {Name Object Mode Var : Type*}

variable (Name Var) in
/-- A term in an argument place: a name, or a variable. -/
inductive Term where
  | name : Name → Term
  | var : Var → Term

namespace Term

/-- The object a term stands for, given the meanings of the names and the values of the
variables. -/
def eval (I : Interpretation Name Object) (σ : Var → Object) : Term Name Var → Object
  | name a => I.meaning a
  | var x => σ x

/-- The name a term becomes when each variable is replaced by a name. -/
def subst (ρ : Var → Name) : Term Name Var → Name
  | name a => a
  | var x => ρ x

theorem eval_comp_subst (I : Interpretation Name Object) (ρ : Var → Name) :
    eval I (I.meaning ∘ ρ) = I.meaning ∘ subst (Var := Var) ρ := by
  funext t
  cases t <;> rfl

end Term

variable (Name Mode Var) in
/-- Propositional signs with generality: an elementary sentence whose places are filled by
names or variables (a propositional function such as `fx`), `N` applied to finitely many
signs, `(∃x) . φ`, and `(x) . φ`. -/
inductive QFormula where
  | atom : AtomicFact (Term Name Var) Mode → QFormula
  | N {n : ℕ} : (Fin n → QFormula) → QFormula
  | ex : Var → QFormula → QFormula
  | all : Var → QFormula → QFormula

namespace QFormula

/-- Denial, as `N` with one value. -/
def neg (φ : QFormula Name Mode Var) : QFormula Name Mode Var := N ![φ]

variable [DecidableEq Var]

/-- Whether a sign is true in a reality, given the meanings of the names and the values of the
variables. The quantifiers range over all objects. -/
def holds (I : Interpretation Name Object) (r : Reality (AtomicFact Object Mode)) :
    QFormula Name Mode Var → (Var → Object) → Prop
  | atom a, σ => r (a.mapTo (Term.eval I σ)) = true
  | N ps, σ => ∀ i, ¬ holds I r (ps i) σ
  | ex x φ, σ => ∃ o, holds I r φ (Function.update σ x o)
  | all x φ, σ => ∀ o, holds I r φ (Function.update σ x o)

/-- The sense of a sign: the realities in which it is true. -/
def qsense (I : Interpretation Name Object) (φ : QFormula Name Mode Var) (σ : Var → Object) :
    Sense (AtomicFact Object Mode) :=
  {r | holds I r φ σ}

/-- `~(∃x) . ~fx` and `(x) . fx` say the same: one of the two quantifiers is definable from
the other with denial. -/
@[tlp "5.441"]
theorem holds_neg_ex_neg (I : Interpretation Name Object) (r : Reality (AtomicFact Object Mode))
    (x : Var) (φ : QFormula Name Mode Var) (σ : Var → Object) :
    holds I r (neg (ex x (neg φ))) σ ↔ holds I r (all x φ) σ := by
  simp [neg, holds]

/-- The translation of a sign with generality into a sign without it, when the names `ns`
name every object: the variables are replaced by names (`ρ`), `(∃x) . φ` becomes
`~N(φ(a), φ(b), …)`, the denial of `N` applied to all the values of the function, and
`(x) . φ` becomes `N(~φ(a), ~φ(b), …)`. -/
@[tlp "5.52"]
def toSentence {n : ℕ} (ns : Fin n → Name) :
    QFormula Name Mode Var → (Var → Name) → Sentence Name Mode
  | atom a, ρ => Formula.elem (a.mapTo (Term.subst ρ))
  | N ps, ρ => Formula.N fun i => toSentence ns (ps i) ρ
  | ex x φ, ρ => Formula.neg (Formula.N fun i => toSentence ns φ (Function.update ρ x (ns i)))
  | all x φ, ρ => Formula.N fun i => Formula.neg (toSentence ns φ (Function.update ρ x (ns i)))

theorem mem_sense_neg (I : Interpretation Name Object) (ψ : Sentence Name Mode)
    (r : Reality (AtomicFact Object Mode)) :
    r ∈ I.sense (Formula.neg ψ) ↔ r ∉ I.sense ψ := by
  rw [(I.sense_neg ψ).1]; rfl

theorem mem_sense_N (I : Interpretation Name Object) {n : ℕ} (ps : Fin n → Sentence Name Mode)
    (r : Reality (AtomicFact Object Mode)) :
    r ∈ I.sense (Formula.N ps) ↔ ∀ i, r ∉ I.sense (ps i) :=
  Iff.rfl

theorem mapTo_mapTo {α β γ : Type*} (f : α → β) (g : β → γ) (a : AtomicFact α Mode) :
    (a.mapTo f).mapTo g = a.mapTo (g ∘ f) := by
  simp [AtomicFact.mapTo]

/-- The general form of proposition covers generality, when there are finitely many objects
and each is named: a quantified sign and its translation into a sign built from elementary
sentences with `N` alone are true in the same realities. `N` applied to all the values of
`fx` is `~(∃x) . fx`. -/
@[tlp "5.52"]
theorem mem_sense_toSentence (I : Interpretation Name Object) {n : ℕ} {ns : Fin n → Name}
    (hcov : ∀ o, ∃ i, I.meaning (ns i) = o) (φ : QFormula Name Mode Var) (ρ : Var → Name)
    (r : Reality (AtomicFact Object Mode)) :
    r ∈ I.sense (toSentence ns φ ρ) ↔ holds I r φ (I.meaning ∘ ρ) := by
  induction φ generalizing ρ with
  | atom a =>
    show r ((a.mapTo (Term.subst ρ)).mapTo I.meaning) = true ↔ _
    rw [mapTo_mapTo, ← Term.eval_comp_subst]
    rfl
  | N ps ih =>
    rw [toSentence, mem_sense_N]
    exact forall_congr' fun i => not_congr (ih i ρ)
  | ex x φ ih =>
    rw [toSentence, mem_sense_neg, mem_sense_N]
    simp only [not_forall, not_not, holds]
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨I.meaning (ns i), by rw [← Function.comp_update]; exact (ih _).mp hi⟩
    · rintro ⟨o, ho⟩
      obtain ⟨i, rfl⟩ := hcov o
      exact ⟨i, (ih _).mpr (by rw [Function.comp_update]; exact ho)⟩
  | all x φ ih =>
    rw [toSentence, mem_sense_N]
    simp only [mem_sense_neg, not_not, holds]
    constructor
    · intro h o
      obtain ⟨i, rfl⟩ := hcov o
      rw [← Function.comp_update]
      exact (ih _).mp (h i)
    · intro h i
      exact (ih _).mpr (by rw [Function.comp_update]; exact h _)

/-- The concept "all" is separated from the truth-function (1): the sense of `N` depends only
on which propositions are its values, not on how they are listed. -/
@[tlp "5.521"]
theorem NSense_eq_of_range_eq {Atom : Type*} {m n : ℕ} {ps : Fin m → Sense Atom}
    {qs : Fin n → Sense Atom} (h : Set.range ps = Set.range qs) : NSense ps = NSense qs := by
  ext r
  simp only [NSense, Set.mem_ofPred_eq]
  constructor
  · intro hp j
    obtain ⟨i, hi⟩ : qs j ∈ Set.range ps := h ▸ ⟨j, rfl⟩
    exact hi ▸ hp i
  · intro hq i
    obtain ⟨j, hj⟩ : ps i ∈ Set.range qs := h ▸ ⟨i, rfl⟩
    exact hj ▸ hq j

/-- The concept "all" is separated from the truth-function (2): generality contributes only
the collection of the values of the function, to which `N` is applied, and the translation of
a quantified sign does not depend on which list of names (covering all objects) is used. -/
@[tlp "5.521"]
theorem sense_toSentence_indep (I : Interpretation Name Object) {m n : ℕ} {ns : Fin m → Name}
    {ns' : Fin n → Name} (hcov : ∀ o, ∃ i, I.meaning (ns i) = o)
    (hcov' : ∀ o, ∃ i, I.meaning (ns' i) = o) (φ : QFormula Name Mode Var) (ρ : Var → Name) :
    I.sense (toSentence ns φ ρ) = I.sense (toSentence ns' φ ρ) := by
  ext r
  rw [mem_sense_toSentence I hcov, mem_sense_toSentence I hcov']

/-- `(∃x) . fx` is not the proposition "`fx` is possible": in the space of all realities,
every value of `fx` is possible whatever the reality, but `(∃x) . fx` is true in one reality
and false in another. It is a proposition with sense, neither a tautology nor a
contradiction; possibility is shown by the sign being a significant proposition (4.464), not
said by it. -/
@[tlp "5.525"]
theorem ex_not_possibility [Nonempty Object] (I : Interpretation Name Object) (f : Mode)
    (x : Var) (σ : Var → Object) :
    let fx : QFormula Name Mode Var := atom ⟨f, [Term.var x], by simp⟩
    (∀ o : Object, PossibleIn ⟨Set.univ⟩ (elementary (⟨f, [o], by simp⟩ : AtomicFact Object Mode)))
      ∧ PossibleIn ⟨Set.univ⟩ (qsense I (ex x fx) σ)
      ∧ ¬ CertainIn ⟨Set.univ⟩ (qsense I (ex x fx) σ) := by
  intro fx
  refine ⟨fun o => ⟨fun _ => true, rfl, Set.mem_univ _⟩, ?_, ?_⟩
  · obtain ⟨o⟩ := ‹Nonempty Object›
    exact ⟨fun _ => true, ⟨o, rfl⟩, Set.mem_univ _⟩
  · intro h
    have := h (Set.mem_univ (fun _ => false))
    simp [qsense, holds, fx] at this

/-- The mark of a logical proposition is not general validity. A proposition without
generality can be a tautology (`p ∨ ~p`), and a general proposition `(x) . fx` can be true
(true of every object) in a reality without being a tautology: its general validity is
accidental. -/
@[tlp "6.1231"]
theorem tautology_not_generality [Nonempty Object] (I : Interpretation Name Object)
    (s : ElemSentence Name Mode) (f : Mode) (x : Var) (σ : Var → Object) :
    let fx : QFormula Name Mode Var := atom ⟨f, [Term.var x], by simp⟩
    IsTautology (I.sense (Formula.or (Formula.elem s) (Formula.neg (Formula.elem s))))
      ∧ PossibleIn ⟨Set.univ⟩ (qsense I (all x fx) σ) ∧ ¬ IsTautology (qsense I (all x fx) σ) := by
  intro fx
  refine ⟨?_, ⟨fun _ => true, fun _ => rfl, Set.mem_univ _⟩, ?_⟩
  · intro r
    rw [Formula.or, mem_sense_neg, mem_sense_N]
    intro h
    exact h 1 ((mem_sense_neg I _ r).mpr (h 0))
  · intro h
    obtain ⟨o⟩ := ‹Nonempty Object›
    have : holds I (fun _ => false) fx (Function.update σ x o) := h (fun _ => false) o
    simp [holds, fx] at this

end QFormula

end Tractatus
