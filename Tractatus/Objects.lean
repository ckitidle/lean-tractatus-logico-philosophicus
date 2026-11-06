import Mathlib.Order.SetNotation
import Mathlib.Data.Set.Image
import Mathlib.Logic.Equiv.Basic
import Tractatus.Facts

/-!
# Objects, atomic facts and their form (stage 1: 2.01–2.034)

What objects are is left open (docs/policy.md §3.2): they are a type parameter `Object`.
The ways objects can be combined are a type parameter `Mode`.

* an atomic fact is a configuration of objects: a mode of combination together with the
  objects that fill its argument places (2.01, 2.0272); its structure is the mode with the
  number of places (2.032),
* a `Frame` says which configurations are possible atomic facts,
* the form of an object is the set of places it can occupy in possible atomic facts
  (2.0141),
* the claims that the forms of the objects settle all possibilities of combination
  (2.0123, 2.014, 2.023), that every object can occur in an atomic fact (2.011), and that
  two objects with the same form can be exchanged (2.0233).
-/

namespace Tractatus

variable (Object Mode : Type*)

/-- An atomic fact, as a configuration of objects: a mode of combination and the objects that
fill its argument places, in order. At least one object takes part. -/
@[tlp "2.01", tlp "2.0272"]
structure AtomicFact where
  /-- the way the objects are combined -/
  mode : Mode
  /-- the objects in their argument places -/
  args : List Object
  args_ne_nil : args ≠ []

/-- A place in a mode of combination: the mode, its number of argument places, and the
position (counted from `0`). -/
abbrev Place := Mode × ℕ × ℕ

variable {Object Mode}

namespace AtomicFact

/-- The objects that occur in an atomic fact. -/
def objects (a : AtomicFact Object Mode) : Set Object :=
  {o | o ∈ a.args}

/-- The structure of an atomic fact: the way its objects hang together, here the mode of
combination together with the number of argument places (what remains when the particular
objects are left out). -/
@[tlp "2.032"]
def structureOf (a : AtomicFact Object Mode) : Mode × ℕ :=
  (a.mode, a.args.length)

/-- In an atomic fact the objects are combined in a definite way: the atomic fact is fixed by
its mode of combination and by which objects stand in which places. -/
@[tlp "2.031"]
theorem eq_iff_mode_args {a b : AtomicFact Object Mode} :
    a = b ↔ a.mode = b.mode ∧ a.args = b.args := by
  constructor
  · rintro rfl; exact ⟨rfl, rfl⟩
  · obtain ⟨m, l, h⟩ := a
    obtain ⟨m', l', h'⟩ := b
    rintro ⟨rfl, rfl⟩
    rfl

/-- `o` stands at the place `pl` in the atomic fact `a`. -/
def Occupies (a : AtomicFact Object Mode) (o : Object) (pl : Place Mode) : Prop :=
  ∃ i, ∃ h : i < a.args.length, a.args[i] = o ∧ pl = (a.mode, a.args.length, i)

/-- Replace every object of an atomic fact by its image under `e`. -/
def map (e : Object → Object) (a : AtomicFact Object Mode) : AtomicFact Object Mode where
  mode := a.mode
  args := a.args.map e
  args_ne_nil := by simpa using a.args_ne_nil

end AtomicFact

/-- If there are no objects, there are no atomic facts at all, so nothing gives the world a
fixed form. -/
@[tlp "2.026"]
theorem isEmpty_atomicFact [IsEmpty Object] : IsEmpty (AtomicFact Object Mode) := by
  constructor
  intro a
  obtain ⟨_, l, h⟩ := a
  cases l with
  | nil => exact h rfl
  | cons o _ => exact IsEmpty.false o

variable (Object Mode) in
/-- Which configurations of objects are possible atomic facts. -/
structure Frame where
  /-- the possible atomic facts -/
  possible : Set (AtomicFact Object Mode)

namespace Frame

variable (F : Frame Object Mode)

/-- The form of an object: the possibility of its occurrence in atomic facts, represented by
the set of places it occupies in some possible atomic fact. -/
@[tlp "2.0141"]
def form (o : Object) : Set (Place Mode) :=
  {pl | ∃ a ∈ F.possible, a.Occupies o pl}

/-- The configurations allowed by the forms of the objects: every object stands at a place
that its form allows. -/
def allowed : Set (AtomicFact Object Mode) :=
  {a | ∀ i (h : i < a.args.length), (a.mode, a.args.length, i) ∈ F.form a.args[i]}

/-- Nothing accidental: if an object occurs in a possible atomic fact, that possibility is
already part of the object's form. So every possible atomic fact is allowed by the forms of
its objects. -/
@[tlp "2.012"]
theorem possible_subset_allowed : F.possible ⊆ F.allowed := by
  intro a ha i hi
  exact ⟨a, ha, i, hi, rfl, rfl⟩

/-- The claim that the forms of the objects settle all possibilities of combination: every
configuration in which each object stands at a place its form allows is a possible atomic
fact. No new possibility can be found beyond what lies in the objects (2.0123); the objects
contain the possibility of all atomic facts (2.014); the fixed form of the world consists of
the objects (2.023). -/
@[tlp "2.0123", tlp "2.014", tlp "2.023"]
def FormDeterminesPossibility : Prop :=
  F.allowed ⊆ F.possible

/-- Under the claim, the possible atomic facts are exactly the configurations allowed by the
forms of the objects. -/
theorem possible_eq_allowed (h : F.FormDeterminesPossibility) : F.possible = F.allowed :=
  Set.Subset.antisymm F.possible_subset_allowed h

/-- If all objects (with their forms) are given, all possible atomic facts are given: two
frames satisfying the claim whose objects have the same forms have the same possible atomic
facts. -/
@[tlp "2.0124"]
theorem possible_eq_of_form_eq {F G : Frame Object Mode} (hF : F.FormDeterminesPossibility)
    (hG : G.FormDeterminesPossibility) (h : F.form = G.form) : F.possible = G.possible := by
  rw [F.possible_eq_allowed hF, G.possible_eq_allowed hG]
  simp only [allowed, h]

/-- The claim that it is essential to every object that it can occur in some atomic fact:
its form is not empty. -/
@[tlp "2.011"]
def EveryObjectCanOccur : Prop :=
  ∀ o, (F.form o).Nonempty

/-- The form of the world, read as the possible structures of atomic facts: the form is the
possibility of the structure. -/
@[tlp "2.033"]
def possibleStructures : Set (Mode × ℕ) :=
  AtomicFact.structureOf '' F.possible

open Classical in
/-- The claim that two objects of the same form differ only in being different: exchanging
them everywhere turns possible atomic facts into possible atomic facts. -/
@[tlp "2.0233"]
def SameFormInterchangeable : Prop :=
  ∀ o o', F.form o = F.form o' → ∀ a, a ∈ F.possible ↔ a.map (Equiv.swap o o') ∈ F.possible

open Classical in
theorem form_swap {o o' : Object} (h : F.form o = F.form o') (x : Object) :
    F.form (Equiv.swap o o' x) = F.form x := by
  rcases eq_or_ne x o with rfl | hxo
  · rw [Equiv.swap_apply_left, h]
  rcases eq_or_ne x o' with rfl | hxo'
  · rw [Equiv.swap_apply_right, h]
  rw [Equiv.swap_apply_of_ne_of_ne hxo hxo']

open Classical in
theorem mem_allowed_map_swap_iff {o o' : Object} (h : F.form o = F.form o')
    (a : AtomicFact Object Mode) : a.map (Equiv.swap o o') ∈ F.allowed ↔ a ∈ F.allowed := by
  simp only [allowed, Set.mem_ofPred_eq, AtomicFact.map, List.length_map, List.getElem_map,
    F.form_swap h]

/-- If the forms of the objects settle all possibilities (2.0123), then two objects of the
same form can be exchanged: they differ only in being different. -/
@[tlp "2.0233"]
theorem sameFormInterchangeable_of_formDeterminesPossibility
    (h : F.FormDeterminesPossibility) : F.SameFormInterchangeable := by
  intro o o' ho a
  rw [F.possible_eq_allowed h, F.mem_allowed_map_swap_iff ho]

end Frame

/-- The structure of a fact (a set of atomic facts) consists of the structures of its atomic
facts. -/
@[tlp "2.034"]
def factStructure (f : Fact (AtomicFact Object Mode)) : Set (Mode × ℕ) :=
  AtomicFact.structureOf '' f

end Tractatus
