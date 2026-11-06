import Tractatus.Generality

/-!
# The sign of identity (stage 4b: 4.241–4.243, 5.441, 5.53–5.531, 5.5302)

Propositional signs without quantifiers, whose elementary parts are elementary sentences or
identities `a = b` between names. Under an interpretation, `a = b` is true in every reality if
the two names mean the same object, and in none otherwise.

* `a = b` means that the sign `a` can be replaced by the sign `b` (4.241); it says nothing
  about the world: it is a tautology or a contradiction (4.242); `a = a` is not a significant
  proposition (4.243).
* Identity of the object is expressed by identity of the sign (5.53): choosing one name for
  each object meant, every sign with identities is translated into a sign without them, with
  the same sense, and different names in the result mean different objects. `f(a, b) . a = b`
  is written `f(a, a)` (5.531).
* `(∃x) . fx . x = a` says the same as `fa` (5.441).
* Russell's definition of identity (sharing all properties) will not do: two different objects
  can share all their properties, and that they do so is a proposition with sense (5.5302).

Identity between variables in quantified signs (5.532 and after) is deferred (stage 4c).
-/

namespace Tractatus

variable {Name Object Mode : Type*}

variable (Name Mode) in
/-- An elementary part of a sign with identities: an elementary sentence, or an identity
`a = b` between two names. -/
inductive IdAtom where
  | elem : ElemSentence Name Mode → IdAtom
  | eq : Name → Name → IdAtom

variable (Name Mode) in
/-- A propositional sign (without quantifiers) that may contain the sign of identity. -/
abbrev IdSentence := Formula (IdAtom Name Mode)

namespace Interpretation

variable (I : Interpretation Name Object)

/-- The sense of a sign with identities: an elementary sentence as before, and `a = b` true in
every reality if `a` and `b` mean the same object, and in none otherwise. -/
def isense : IdSentence Name Mode → Sense (AtomicFact Object Mode)
  | .elem (.elem s) => elementary (I.depicts s)
  | .elem (.eq a b) => {_r | I.meaning a = I.meaning b}
  | .N ps => NSense fun i => isense (ps i)

/-- A formula of the form `a = b` says nothing about the world: it is a tautology or a
contradiction, according to the meanings of the names. -/
@[tlp "4.242"]
theorem senseless_eq (a b : Name) : Senseless (I.isense (.elem (.eq a b) : IdSentence Name Mode)) := by
  by_cases h : I.meaning a = I.meaning b
  · exact Or.inl fun r => h
  · exact Or.inr fun r hr => h hr

/-- `a = a` is not a significant proposition: it is a tautology, whereas no elementary sentence
is. And `a = b` cannot be understood without knowing whether the names mean the same object:
when there are two objects, the same sign `a = b` is a tautology under one interpretation and
a contradiction under another. -/
@[tlp "4.243"]
theorem eq_self_not_significant (a : Name) :
    IsTautology (I.isense (.elem (.eq a a) : IdSentence Name Mode)) ∧
      ∀ s : ElemSentence Name Mode, ¬ IsTautology (I.isense (.elem (.elem s))) := by
  refine ⟨fun r => rfl, fun s h => ?_⟩
  have := h (fun _ => false)
  simp [isense, elementary] at this

/-- When there are two objects, whether `a = b` is a tautology or a contradiction depends on
the interpretation of the names, not on the world. -/
@[tlp "4.243"]
theorem eq_depends_on_meaning {o₁ o₂ : Object} (ho : o₁ ≠ o₂) (a b : Name) (hab : a ≠ b) :
    ∃ I J : Interpretation Name Object,
      IsTautology (I.isense (.elem (.eq a b) : IdSentence Name Mode)) ∧
      IsContradiction (J.isense (.elem (.eq a b) : IdSentence Name Mode)) := by
  classical
  refine ⟨⟨fun _ => o₁⟩, ⟨fun x => if x = a then o₁ else o₂⟩, fun r => rfl, fun r hr => ?_⟩
  exact ho (by simpa [isense, Ne.symm hab] using hr)

end Interpretation

/-- Replacing the name `a` by the name `b`. -/
@[tlp "4.241"]
def replaceName [DecidableEq Name] (a b : Name) (x : Name) : Name :=
  if x = a then b else x

theorem elementary_injective {Atom : Type*} : Function.Injective (elementary (Atom := Atom)) := by
  classical
  intro x y h
  have hx : (fun z => decide (z = x)) ∈ elementary x := by
    simp only [elementary, Set.mem_ofPred_eq, decide_true]
  rw [h] at hx
  simp only [elementary, Set.mem_ofPred_eq, decide_eq_true_eq] at hx
  exact hx.symm

/-- `a = b` means that the sign `a` can be replaced by the sign `b`: the two names mean the same
object exactly when replacing `a` by `b` in any propositional sign leaves its sense unchanged. -/
@[tlp "4.241"]
theorem eq_iff_replaceable [DecidableEq Name] [Nonempty Mode] (I : Interpretation Name Object)
    (a b : Name) :
    I.meaning a = I.meaning b ↔
      ∀ φ : Sentence Name Mode, I.sense (φ.map (AtomicFact.mapTo (replaceName a b))) = I.sense φ := by
  constructor
  · intro h φ
    have hm : I.meaning ∘ replaceName a b = I.meaning := by
      funext x
      by_cases hx : x = a
      · subst hx; simp [replaceName, h]
      · simp [replaceName, hx]
    ext r
    simp only [Interpretation.sense, Formula.mem_sense_map]
    have : (r ∘ I.depicts) ∘ AtomicFact.mapTo (Mode := Mode) (replaceName a b) = r ∘ I.depicts := by
      funext s
      simp only [Function.comp, Interpretation.depicts, QFormula.mapTo_mapTo, hm]
    rw [this]
  · intro h
    obtain ⟨m⟩ := ‹Nonempty Mode›
    have := h (Formula.elem (fx m a))
    simp only [Interpretation.sense, Formula.map, Formula.sense] at this
    have := elementary_injective this
    simp [Interpretation.depicts, AtomicFact.mapTo, fx, replaceName, AtomicFact.eq_iff_mode_args] at this
    exact this.symm

/-- The translation of a sign with identities into a sign without them, given a choice `c` of
one name for each object meant (the identity of the object expressed by the identity of the
sign): each name is replaced by the chosen name, and `a = b` becomes the tautology `N()` if the
chosen names are the same sign, and the contradiction `~N()` otherwise. -/
@[tlp "5.53", tlp "5.531"]
def elimId [DecidableEq Name] (c : Name → Name) : IdSentence Name Mode → Sentence Name Mode
  | .elem (.elem s) => .elem (s.mapTo c)
  | .elem (.eq a b) => if c a = c b then .N ![] else Formula.neg (.N ![])
  | .N ps => .N fun i => elimId c (ps i)

/-- For any interpretation, one name can be chosen for each object meant. -/
theorem exists_choice (I : Interpretation Name Object) :
    ∃ c : Name → Name, (∀ a, I.meaning (c a) = I.meaning a) ∧
      ∀ a b, I.meaning a = I.meaning b → c a = c b := by
  classical
  refine ⟨fun a => @Classical.epsilon _ ⟨a⟩ fun b => I.meaning b = I.meaning a, fun a => ?_,
    fun a b h => ?_⟩
  · exact @Classical.epsilon_spec _ (fun b => I.meaning b = I.meaning a) ⟨a, rfl⟩
  · simp only [h]

/-- Identity of the object is expressed by identity of the sign, and the sign of identity is
not needed: if `c` chooses one name for each object meant, the translation of a sign with
identities has the same sense, and in it different names mean different objects. -/
@[tlp "5.53", tlp "5.531"]
theorem sense_elimId [DecidableEq Name] (I : Interpretation Name Object) {c : Name → Name}
    (hc : ∀ a, I.meaning (c a) = I.meaning a) (hc' : ∀ a b, I.meaning a = I.meaning b → c a = c b)
    (φ : IdSentence Name Mode) :
    I.sense (elimId c φ) = I.isense φ ∧
      ∀ a b, I.meaning (c a) = I.meaning (c b) → c a = c b := by
  refine ⟨?_, fun a b h => hc' a b (by rw [← hc a, ← hc b]; exact h)⟩
  have hm : I.meaning ∘ c = I.meaning := funext hc
  induction φ with
  | elem x =>
    cases x with
    | elem s =>
      show elementary ((s.mapTo c).mapTo I.meaning) = elementary (s.mapTo I.meaning)
      rw [QFormula.mapTo_mapTo, hm]
    | eq a b =>
      ext r
      simp only [elimId, Interpretation.isense, Set.mem_ofPred_eq]
      split_ifs with h
      · rw [QFormula.mem_sense_N]
        exact ⟨fun _ => by rw [← hc a, ← hc b, h], fun _ i => i.elim0⟩
      · rw [QFormula.mem_sense_neg, QFormula.mem_sense_N]
        simp only [not_forall, not_not]
        exact ⟨fun ⟨i, _⟩ => i.elim0, fun hab => absurd (hc' a b hab) h⟩
  | N ps ih =>
    ext r
    simp only [elimId]
    rw [QFormula.mem_sense_N]
    simp only [Interpretation.isense, NSense, Set.mem_ofPred_eq]
    exact forall_congr' fun i => by rw [ih i]

open Classical in
/-- Instead of `f(a, b) . a = b` write `f(a, a)`: if `a` and `b` mean the same object, the two
have the same sense; otherwise the former is a contradiction. -/
@[tlp "5.531"]
theorem sense_and_eq (I : Interpretation Name Object) (f : Mode) (a b : Name) :
    I.isense (Formula.and (.elem (.elem (φxy f a b))) (.elem (.eq a b)) : IdSentence Name Mode) =
      if I.meaning a = I.meaning b then I.isense (.elem (.elem (φxy f a a))) else ∅ := by
  by_cases h : I.meaning a = I.meaning b
  · simp only [h, ↓reduceIte]
    ext r
    simp [Formula.and, Formula.neg, Interpretation.isense, NSense, Fin.forall_fin_two,
      elementary, Interpretation.depicts, AtomicFact.mapTo, φxy, h]
  · simp only [h, ↓reduceIte]
    ext r
    simp [Formula.and, Formula.neg, Interpretation.isense, NSense, Fin.forall_fin_two, h]

/-- `(∃x) . fx . x = a` says the same as `fa`: an object of which `f` holds and which is the
object meant by `a` exists exactly when the elementary sentence `fa` is true. -/
@[tlp "5.441"]
theorem ex_eq_iff (I : Interpretation Name Object) (f : Mode) (a : Name)
    (r : Reality (AtomicFact Object Mode)) :
    (∃ o : Object, r ⟨f, [o], by simp⟩ = true ∧ o = I.meaning a) ↔
      r ∈ I.sense (.elem (fx f a)) := by
  constructor
  · rintro ⟨o, h, rfl⟩
    exact h
  · intro h
    exact ⟨I.meaning a, h, rfl⟩

/-- That two objects share all their properties and relations: exchanging them turns every
atomic fact into one with the same truth-value (and so every truth-function of atomic facts
too). -/
def SharesAllProperties [DecidableEq Object] (r : Reality (AtomicFact Object Mode))
    (o₁ o₂ : Object) : Prop :=
  ∀ a : AtomicFact Object Mode, r (a.mapTo (Equiv.swap o₁ o₂)) = r a

/-- Russell's definition of identity will not do: two different objects can share all their
properties (in a reality where none of them has any), and the proposition that they share all
their properties has sense: it is true in one reality and false in another, whereas identity
is not a matter of the world. -/
@[tlp "5.5302"]
theorem russell_identity_fails [DecidableEq Object] [Nonempty Mode] {o₁ o₂ : Object}
    (ho : o₁ ≠ o₂) :
    SharesAllProperties (Mode := Mode) (fun _ => false) o₁ o₂ ∧
      ∃ r, ¬ SharesAllProperties (Mode := Mode) r o₁ o₂ := by
  classical
  refine ⟨fun a => rfl, ?_⟩
  obtain ⟨m⟩ := ‹Nonempty Mode›
  refine ⟨fun x => decide (x.args = [o₁]), fun h => ?_⟩
  have := h ⟨m, [o₂], by simp⟩
  simp [AtomicFact.mapTo, ho.symm] at this

end Tractatus
