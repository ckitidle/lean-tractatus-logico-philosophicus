import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.FinCases
import Tractatus.Objects
import Tractatus.Logic

/-!
# Names, the structure of pictures, propositional signs and thoughts (stage 3)

The layer that connects signs with objects:

* an elementary sentence is a configuration of names (4.22), like an atomic fact is a
  configuration of objects; an interpretation correlates names with objects (3.202, 3.203),
  and an elementary sentence then depicts the atomic fact obtained by replacing each name by
  its object (2.13, 3.21),
* a picture in the structural sense is such a configuration together with the correlation
  (2.12–2.1514); picture and pictured have the same structure (2.16–2.2),
* the logical space of a frame: the realities in which only possible atomic facts obtain.
  This connects the objects of stage 1 with the logical space: a sentence whose names stand
  at places their objects' forms allow depicts a possible atomic fact (3.02, 3.03, 3.4),
* propositional signs are signs of the general form over elementary sentences (3.12); their
  sense is computed from the meanings of the names (3.318, 4.024, 4.03); only the arrangement
  of the names, not their collection, expresses the sense (3.142, 3.1432),
* thoughts, significant propositions and a priori truth (3, 3.04, 3.05, 3.5, 4).
-/

namespace Tractatus

variable {Name Object Mode : Type*}

namespace AtomicFact

/-- Replace each element of a configuration by its image under `f`, keeping the mode. -/
def mapTo {α β : Type*} (f : α → β) (a : AtomicFact α Mode) : AtomicFact β Mode where
  mode := a.mode
  args := a.args.map f
  args_ne_nil := by simpa using a.args_ne_nil

theorem structureOf_mapTo {α β : Type*} (f : α → β) (a : AtomicFact α Mode) :
    (a.mapTo f).structureOf = a.structureOf := by
  simp [mapTo, structureOf]

theorem objects_mapTo {α β : Type*} (f : α → β) (a : AtomicFact α Mode) :
    (a.mapTo f).objects = f '' a.objects := by
  ext x
  simp [mapTo, objects]

end AtomicFact

variable (Name Mode) in
/-- An elementary sentence: names combined in a definite way, a configuration of names (the
propositional sign as a fact in which its words are combined). -/
@[tlp "4.22", tlp "3.14"]
abbrev ElemSentence := AtomicFact Name Mode

variable (Name Object) in
/-- An interpretation: each name (simple sign) means an object, its meaning; in the
proposition the name stands for the object. -/
@[tlp "3.202", tlp "3.203", tlp "3.22"]
structure Interpretation where
  /-- the object a name means -/
  meaning : Name → Object

/-- The notation `fx`: the elementary sentence combining the single name `x` by `f`. -/
@[tlp "4.24"]
def fx (f : Mode) (x : Name) : ElemSentence Name Mode :=
  ⟨f, [x], by simp⟩

/-- The notation `φ(x, y)`: the elementary sentence combining the names `x`, `y` by `φ`. -/
@[tlp "4.24"]
def φxy (φ : Mode) (x y : Name) : ElemSentence Name Mode :=
  ⟨φ, [x, y], by simp⟩

namespace Interpretation

variable (I : Interpretation Name Object)

/-- The atomic fact an elementary sentence depicts: the configuration of the objects meant by
its names, in the same mode and order. To the elements of the sign correspond the objects. -/
def depicts (s : ElemSentence Name Mode) : AtomicFact Object Mode :=
  s.mapTo I.meaning

/-- The configuration of the names in the sentence corresponds to the configuration of the
objects in the depicted atomic fact: the same structure, and the objects are exactly those
meant by the names. -/
@[tlp "3.21", tlp "3.2"]
theorem depicts_structure (s : ElemSentence Name Mode) :
    (I.depicts s).structureOf = s.structureOf ∧ (I.depicts s).objects = I.meaning '' s.objects :=
  ⟨AtomicFact.structureOf_mapTo _ _, AtomicFact.objects_mapTo _ _⟩

/-- If distinct names mean distinct objects, distinct elementary sentences depict distinct
atomic facts: the sentence has as many distinguishable parts as the situation. -/
@[tlp "4.04"]
theorem depicts_injective (h : Function.Injective I.meaning) :
    Function.Injective (I.depicts (Mode := Mode)) := by
  intro s t hst
  rw [AtomicFact.eq_iff_mode_args] at hst ⊢
  exact ⟨hst.1, List.map_injective_iff.mpr h hst.2⟩

end Interpretation

variable (Name Object Mode) in
/-- A picture in the structural sense, a model of reality: its elements (names) combined in a
definite way, together with the representing relation that correlates the elements with
things, which belongs to the picture. -/
@[tlp "2.12", tlp "2.14", tlp "2.1513", tlp "2.1514"]
structure StructPicture where
  /-- the elements combined in a definite way -/
  sentence : ElemSentence Name Mode
  /-- the representing relation: the coordination of elements with things -/
  coord : Interpretation Name Object

namespace StructPicture

variable (P : StructPicture Name Object Mode)

/-- The atomic fact the picture depicts. -/
def depicted : AtomicFact Object Mode :=
  P.coord.depicts P.sentence

/-- To the objects correspond the elements of the picture, and they stand for the objects: at
each place, the depicted atomic fact has the object that the element at that place is
correlated with. -/
@[tlp "2.13", tlp "2.131"]
theorem depicted_getElem (i : ℕ) (h : i < P.sentence.args.length) :
    P.depicted.args[i]'(by simpa [depicted, Interpretation.depicts, AtomicFact.mapTo] using h) =
      P.coord.meaning (P.sentence.args[i]) := by
  simp [depicted, Interpretation.depicts, AtomicFact.mapTo]

/-- The structure of the picture: the way its elements are combined. -/
@[tlp "2.15"]
def structure_ : Mode × ℕ :=
  P.sentence.structureOf

/-- The form of representation: the possibility that things are combined as the elements of
the picture are, i.e. the configurations of things with the picture's structure. -/
@[tlp "2.151", tlp "2.15"]
def formOfRepresentation : Set (AtomicFact Object Mode) :=
  {a | a.structureOf = P.structure_}

/-- The picture has its form of representation in common with what it pictures: the depicted
atomic fact has the picture's structure. This shared structure is the logical form common to
every picture and what it pictures. -/
@[tlp "2.16", tlp "2.161", tlp "2.17", tlp "2.18", tlp "2.2"]
theorem depicted_mem_formOfRepresentation : P.depicted ∈ P.formOfRepresentation :=
  AtomicFact.structureOf_mapTo _ _

/-- A logical picture: one whose form of representation is the logical form, i.e. what it
depicts has its structure. -/
@[tlp "2.181"]
def IsLogicalPicture : Prop :=
  P.depicted ∈ P.formOfRepresentation

/-- Every picture is also a logical picture. -/
@[tlp "2.182"]
theorem isLogicalPicture : P.IsLogicalPicture :=
  P.depicted_mem_formOfRepresentation

/-- A picture can depict every configuration of things that has its form: if its elements are
distinct, some correlation of elements with things makes it depict any given atomic fact of
the same structure. -/
@[tlp "2.171"]
theorem exists_coord_of_mem_form [Nonempty Object] (s : ElemSentence Name Mode)
    (hs : s.args.Nodup) (a : AtomicFact Object Mode) (ha : a.structureOf = s.structureOf) :
    ∃ I : Interpretation Name Object, I.depicts s = a := by
  classical
  obtain ⟨hm, hl⟩ := Prod.mk.inj ha
  let f : Name → Object := fun x =>
    if h : ∃ i : Fin s.args.length, s.args[i] = x then a.args[(h.choose : ℕ)]'(by
      rw [hl]; exact h.choose.2) else Classical.arbitrary Object
  refine ⟨⟨f⟩, ?_⟩
  rw [AtomicFact.eq_iff_mode_args]
  refine ⟨hm.symm, ?_⟩
  apply List.ext_getElem
  · simp [Interpretation.depicts, AtomicFact.mapTo, hl]
  · intro i h1 h2
    simp only [Interpretation.depicts, AtomicFact.mapTo, List.getElem_map]
    have hex : ∃ j : Fin s.args.length, s.args[j] = s.args[i]'(by simpa [Interpretation.depicts,
        AtomicFact.mapTo] using h1) := ⟨⟨i, by simpa [Interpretation.depicts,
        AtomicFact.mapTo] using h1⟩, rfl⟩
    simp only [f, hex, ↓reduceDIte]
    have hj := hex.choose_spec
    have := (List.Nodup.getElem_inj_iff hs).mp hj
    simp only [this]

/-- The picture is true in a world when the atomic fact it depicts obtains there. -/
def TrueIn (w : World (AtomicFact Object Mode)) : Prop :=
  P.depicted ∈ w

/-- The picture represents from outside, so it can be right or wrong: it is true in some
world and false in another. -/
@[tlp "2.173"]
theorem exists_trueIn_and_not :
    (∃ w, P.TrueIn w) ∧ ∃ w, ¬ P.TrueIn w :=
  ⟨⟨{P.depicted}, rfl⟩, ⟨∅, fun h => h⟩⟩

end StructPicture

/-- The logical space of a frame: the realities in which only possible atomic facts obtain. -/
def Frame.space (F : Frame Object Mode) : LogicalSpace (AtomicFact Object Mode) :=
  ⟨{r | ∀ a, r a = true → a ∈ F.possible}⟩

namespace Interpretation

variable (I : Interpretation Name Object)

/-- An elementary sentence is well formed for a frame when each name stands at a place that
the form of its object allows. -/
def WellFormed (F : Frame Object Mode) (s : ElemSentence Name Mode) : Prop :=
  ∀ i (h : i < s.args.length), (s.mode, s.args.length, i) ∈ F.form (I.meaning s.args[i])

theorem wellFormed_iff (F : Frame Object Mode) (s : ElemSentence Name Mode) :
    I.WellFormed F s ↔ I.depicts s ∈ F.allowed := by
  simp only [WellFormed, Frame.allowed, depicts, AtomicFact.mapTo, Set.mem_ofPred_eq,
    List.length_map, List.getElem_map]

/-- What can be thought is possible: if the forms of the objects settle all possibilities
(2.0123), an elementary sentence whose names stand at places their objects allow depicts a
possible atomic fact. -/
@[tlp "3.02"]
theorem depicts_mem_possible {F : Frame Object Mode} (hF : F.FormDeterminesPossibility)
    {s : ElemSentence Name Mode} (hs : I.WellFormed F s) : I.depicts s ∈ F.possible :=
  hF ((I.wellFormed_iff F s).mp hs)

/-- We cannot think anything unlogical: under 2.0123, an elementary sentence depicts a possible
atomic fact exactly when its names stand at places their objects allow. -/
@[tlp "3.03"]
theorem depicts_mem_possible_iff {F : Frame Object Mode} (hF : F.FormDeterminesPossibility)
    (s : ElemSentence Name Mode) : I.depicts s ∈ F.possible ↔ I.WellFormed F s := by
  rw [wellFormed_iff, F.possible_eq_allowed hF]

end Interpretation

/-- The picture presents a situation in logical space: what it depicts has a place in the
logical space of the frame (some possible reality makes it true) exactly when the depicted
atomic fact is possible. The existence of the place is guaranteed by the constituents alone. -/
@[tlp "2.11", tlp "3.4"]
theorem region_nonempty_iff (F : Frame Object Mode) (a : AtomicFact Object Mode) :
    (elementary a ∩ F.space.possible).Nonempty ↔ a ∈ F.possible := by
  classical
  constructor
  · rintro ⟨r, hr, hsp⟩
    exact hsp a hr
  · intro ha
    refine ⟨fun b => decide (b = a), by simp [elementary], fun b hb => ?_⟩
    simp only [decide_eq_true_eq] at hb
    rw [hb]; exact ha

/-! ## Propositional signs -/

namespace Formula

variable {A B : Type*}

/-- Replace each elementary proposition `a` of a sign by `f a`. -/
def map (f : A → B) : Formula A → Formula B
  | elem a => elem (f a)
  | N ps => N fun i => (ps i).map f

theorem mem_sense_map (f : A → B) (φ : Formula A) (r : Reality B) :
    r ∈ (φ.map f).sense ↔ (r ∘ f) ∈ φ.sense := by
  induction φ with
  | elem a => rfl
  | N ps ih =>
    simp only [map, sense, NSense, Set.mem_ofPred_eq]
    exact forall_congr' fun i => by rw [ih i]

/-- The elementary propositions occurring in a sign. -/
def atoms : Formula A → Set A
  | elem a => {a}
  | N ps => ⋃ i, (ps i).atoms

theorem atoms_neg (φ : Formula A) : (neg φ).atoms = φ.atoms := by
  ext a
  simp [neg, atoms]

theorem map_neg (f : A → B) (φ : Formula A) : (neg φ).map f = neg (φ.map f) := by
  simp only [neg, map]
  congr 1
  funext i
  obtain rfl : i = 0 := Subsingleton.elim _ _
  rfl

end Formula

variable (Name Mode) in
/-- A propositional sign: a sign of the general form whose elementary propositions are
elementary sentences (configurations of names), i.e. a completely analysed proposition. -/
@[tlp "3.12", tlp "3.201"]
abbrev Sentence := Formula (ElemSentence Name Mode)

/-- The names occurring in a propositional sign. -/
def Sentence.names (φ : Sentence Name Mode) : Set Name :=
  ⋃ s ∈ φ.atoms, s.objects

/-- A name occurs in a proposition only within an elementary sentence: the names of a sign are
those of its elementary sentences. -/
@[tlp "4.23"]
theorem Sentence.mem_names_iff (φ : Sentence Name Mode) (x : Name) :
    x ∈ φ.names ↔ ∃ s ∈ φ.atoms, x ∈ s.objects := by
  simp [Sentence.names]

/-- An expression (here a name), presented by the variable whose values are the propositions
containing it. -/
@[tlp "3.31", tlp "3.313"]
def containing (x : Name) : Set (Sentence Name Mode) :=
  {φ | x ∈ φ.names}

namespace Interpretation

variable (I : Interpretation Name Object)

/-- The sense of a propositional sign under an interpretation: the elementary sentences are
replaced by the atomic facts they depict. -/
def sense (φ : Sentence Name Mode) : Sense (AtomicFact Object Mode) :=
  (φ.map I.depicts).sense

/-- An elementary sentence is true exactly when the atomic fact it depicts obtains: it can be
true or false only by being a picture of reality. -/
@[tlp "4.06"]
theorem mem_sense_elem (s : ElemSentence Name Mode) (r : Reality (AtomicFact Object Mode)) :
    r ∈ I.sense (Formula.elem s) ↔ r (I.depicts s) = true :=
  Iff.rfl

/-- The proposition is a function of the expressions in it: its sense depends only on the
meanings of the names occurring in it. To understand a proposition it is enough to understand
its constituents, and old words communicate the sense of any new combination of them. -/
@[tlp "3.318", tlp "4.024", tlp "4.03"]
theorem sense_congr {I J : Interpretation Name Object} {φ : Sentence Name Mode}
    (h : ∀ x ∈ φ.names, I.meaning x = J.meaning x) : I.sense φ = J.sense φ := by
  induction φ with
  | elem s =>
    have : I.depicts s = J.depicts s := by
      rw [AtomicFact.eq_iff_mode_args]
      refine ⟨rfl, List.map_congr_left fun x hx => h x ?_⟩
      simp only [Sentence.names, Formula.atoms]
      simp only [Set.mem_singleton_iff, Set.iUnion_iUnion_eq_left]
      exact hx
    simp only [sense, Formula.map, this]
  | N ps ih =>
    have : ∀ i, I.sense (ps i) = J.sense (ps i) := fun i => ih i fun x hx => h x (by
      simp only [Sentence.names, Set.mem_iUnion] at hx ⊢
      obtain ⟨s, hs, hx⟩ := hx
      exact ⟨s, by simp only [Formula.atoms, Set.mem_iUnion]; exact ⟨i, hs⟩, hx⟩)
    simp only [sense, Formula.map, Formula.sense] at this ⊢
    simp only [this]

/-- The sense of the denial is the complement: the denial determines a logical place outside
that of the denied proposition, and the denial (like the other logical signs) brings in no new
names, nothing in reality corresponds to it. -/
@[tlp "4.0641", tlp "3.42", tlp "4.0621"]
theorem sense_neg (φ : Sentence Name Mode) :
    I.sense (Formula.neg φ) = (I.sense φ)ᶜ ∧ Sentence.names (Formula.neg φ) = φ.names ∧
      I.sense (Formula.neg (Formula.neg φ)) = I.sense φ := by
  have h1 : ∀ ψ : Sentence Name Mode, I.sense (Formula.neg ψ) = (I.sense ψ)ᶜ := fun ψ => by
    simp only [sense, Formula.map_neg]
    exact Formula.sense_neg _
  refine ⟨h1 φ, ?_, by rw [h1, h1, compl_compl]⟩
  simp [Sentence.names, Formula.atoms_neg]

/-- The proposition determines reality up to yes or no: in each reality exactly one of the
proposition and its denial is true. -/
@[tlp "4.023"]
theorem mem_sense_or_neg (φ : Sentence Name Mode) (r : Reality (AtomicFact Object Mode)) :
    (r ∈ I.sense φ ∨ r ∈ I.sense (Formula.neg φ)) ∧
      ¬ (r ∈ I.sense φ ∧ r ∈ I.sense (Formula.neg φ)) := by
  rw [(I.sense_neg φ).1]
  exact ⟨em _, fun h => h.2 h.1⟩

/-- The proposition is a picture of reality: the sense of an elementary sentence is the sense
of the picture (stage 1) that represents the depicted atomic fact as existing. -/
@[tlp "4.01"]
theorem sense_elem_eq_picture [DecidableEq (AtomicFact Object Mode)] (s : ElemSentence Name Mode) :
    I.sense (Formula.elem s) =
      (⟨fun a => if a = I.depicts s then some true else none, ⟨I.depicts s, by simp⟩⟩ :
        Picture (AtomicFact Object Mode)).sense := by
  ext r
  simp only [mem_sense_elem, Picture.sense, Set.mem_ofPred_eq]
  constructor
  · intro h a b hab
    split_ifs at hab with ha
    · cases hab; rw [ha]; exact h
  · intro h
    exact h _ true (by simp)

/-- The elementary sentences true in a world. -/
def trueSentences (w : World (AtomicFact Object Mode)) : Set (ElemSentence Name Mode) :=
  {s | I.depicts s ∈ w}

/-- The logical picture can depict the world, and the totality of true thoughts is a picture
of the world: if every object is meant by some name, the true elementary sentences determine
the world. -/
@[tlp "2.19", tlp "3.01"]
theorem world_eq_of_trueSentences_eq (h : Function.Surjective I.meaning)
    {w w' : World (AtomicFact Object Mode)} (hw : I.trueSentences w = I.trueSentences w') :
    w = w' := by
  ext a
  obtain ⟨g, hg⟩ : ∃ g : Object → Name, ∀ o, I.meaning (g o) = o :=
    ⟨Function.surjInv h, Function.surjInv_eq h⟩
  have hs : I.depicts (a.mapTo g) = a := by
    rw [AtomicFact.eq_iff_mode_args]
    refine ⟨rfl, ?_⟩
    simp [depicts, AtomicFact.mapTo, Function.comp_def, hg]
  have := congrArg (fun S => a.mapTo g ∈ S) hw
  simp only [trueSentences, Set.mem_ofPred_eq, hs, eq_iff_iff] at this
  exact this

end Interpretation

variable (Name Object) in
/-- A symbol: a sign together with what it means. The sign is the part of the symbol
perceptible by the senses. -/
@[tlp "3.32"]
structure Symbol where
  /-- the perceptible part -/
  sign : Name
  /-- what the symbol means -/
  meaning : Object

/-- The symbol a name is under an interpretation. -/
def Interpretation.symbol (I : Interpretation Name Object) (x : Name) : Symbol Name Object :=
  ⟨x, I.meaning x⟩

/-- Only facts express a sense, a class of names cannot; that the names stand in a certain
relation says that the objects do: two elementary sentences with the same names (and mode) can
have different senses, differing only in the arrangement of the names. -/
@[tlp "3.142", tlp "3.1432"]
theorem arrangement_matters :
    ∃ (I : Interpretation (Fin 2) (Fin 2)) (s t : ElemSentence (Fin 2) Unit),
      s.objects = t.objects ∧ I.sense (Formula.elem s) ≠ I.sense (Formula.elem t) := by
  classical
  let s : ElemSentence (Fin 2) Unit := φxy () 0 1
  let t : ElemSentence (Fin 2) Unit := φxy () 1 0
  let I : Interpretation (Fin 2) (Fin 2) := ⟨id⟩
  refine ⟨I, s, t, ?_, ?_⟩
  · ext x; fin_cases x <;> simp [s, t, φxy, AtomicFact.objects]
  · intro h
    have hst : I.depicts s ≠ I.depicts t := by
      rw [Ne, AtomicFact.eq_iff_mode_args]
      simp [I, s, t, φxy, Interpretation.depicts, AtomicFact.mapTo]
    have := congrArg (fun S => (fun b => decide (b = I.depicts s)) ∈ S) h
    simp only [Interpretation.mem_sense_elem, decide_eq_true_eq, eq_iff_iff] at this
    exact hst (this.mp trivial).symm

/-- Two different symbols can have the sign in common: the same elementary sentence has
different senses under two interpretations of its name. -/
@[tlp "3.321"]
theorem same_sign_different_symbols :
    ∃ (I J : Interpretation Unit (Fin 2)) (s : ElemSentence Unit Unit),
      I.sense (Formula.elem s) ≠ J.sense (Formula.elem s) := by
  classical
  let s : ElemSentence Unit Unit := fx () ()
  let I : Interpretation Unit (Fin 2) := ⟨fun _ => 0⟩
  let J : Interpretation Unit (Fin 2) := ⟨fun _ => 1⟩
  refine ⟨I, J, s, fun h => ?_⟩
  have hst : I.depicts s ≠ J.depicts s := by
    rw [Ne, AtomicFact.eq_iff_mode_args]
    simp [I, J, s, fx, Interpretation.depicts, AtomicFact.mapTo]
  have := congrArg (fun S => (fun b => decide (b = I.depicts s)) ∈ S) h
  simp only [Interpretation.mem_sense_elem, decide_eq_true_eq, eq_iff_iff] at this
  exact hst (this.mp trivial).symm

/-- A feature of propositional signs is essential (under an interpretation) if it is the same
for all signs that express the same sense; the others are accidental, due to the particular way
the sign is produced. -/
@[tlp "3.34"]
def IsEssentialFeature (I : Interpretation Name Object) (P : Sentence Name Mode → Prop) : Prop :=
  ∀ φ ψ, I.sense φ = I.sense ψ → (P φ ↔ P ψ)

/-- What is essential in a proposition is what is common to all propositions that can express
the same sense: a feature is essential exactly when it is a feature of the sense. -/
@[tlp "3.341"]
theorem isEssentialFeature_iff (I : Interpretation Name Object) (P : Sentence Name Mode → Prop) :
    IsEssentialFeature I P ↔ ∃ Q : Sense (AtomicFact Object Mode) → Prop, ∀ φ, P φ ↔ Q (I.sense φ) := by
  constructor
  · intro h
    refine ⟨fun p => ∃ φ, I.sense φ = p ∧ P φ, fun φ => ⟨fun hp => ⟨φ, rfl, hp⟩, ?_⟩⟩
    rintro ⟨ψ, hψ, hp⟩
    exact (h ψ φ hψ).mp hp
  · rintro ⟨Q, hQ⟩ φ ψ h
    rw [hQ, hQ, h]

/-- The logical place of a proposition in a logical space: the possible realities in which it
is true (given by the propositional sign and the logical coordinates, the names' meanings). -/
@[tlp "3.41"]
def logicalPlace (I : Interpretation Name Object) (L : LogicalSpace (AtomicFact Object Mode))
    (φ : Sentence Name Mode) : Set (Reality (AtomicFact Object Mode)) :=
  I.sense φ ∩ L.possible

variable (Name Object Mode) in
/-- A thought: a propositional sign applied, i.e. together with the projection (the meanings of
its names); the logical picture of facts. -/
@[tlp "3", tlp "3.5"]
structure Thought where
  /-- the propositional sign -/
  sign : Sentence Name Mode
  /-- the method of projection -/
  interp : Interpretation Name Object

namespace Thought

variable (θ : Thought Name Object Mode)

/-- The sense of a thought. -/
def sense : Sense (AtomicFact Object Mode) :=
  θ.interp.sense θ.sign

/-- A significant proposition: one with sense, i.e. neither a tautology nor a contradiction. -/
@[tlp "4"]
def IsSignificant : Prop :=
  ¬ Senseless θ.sense

/-- A thought true a priori in a logical space: one whose possibility guarantees its truth, i.e.
true in every possible reality. -/
@[tlp "3.04"]
def AprioriTrue (L : LogicalSpace (AtomicFact Object Mode)) : Prop :=
  CertainIn L θ.sense

/-- Under independence, a significant thought is not true a priori: its truth could only be
known a priori if it could be recognized from the thought itself, which happens only for
tautologies. -/
@[tlp "3.05"]
theorem not_aprioriTrue {L : LogicalSpace (AtomicFact Object Mode)} (h : Independent L)
    (hs : θ.IsSignificant) : ¬ θ.AprioriTrue L :=
  fun ha => hs (Or.inl (onlyLogicalNecessity_of_independent h _ ha))

end Thought

end Tractatus
