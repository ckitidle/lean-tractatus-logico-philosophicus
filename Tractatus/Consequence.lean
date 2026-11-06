import Tractatus.Picture

/-!
# Consequence (stage 1: 5.11–5.143)

Consequence is defined from truth-grounds (5.11, 5.12), relative to a logical space: only
possible realities count. With the full logical space (every reality possible) this is
consequence over all truth-possibilities.

* what follows from what, and the content (what a proposition excludes) (5.121–5.14),
* consequence is decidable from the truth-functions alone (5.13),
* under independence, nothing follows from an elementary proposition but itself (5.134),
  and nothing follows from a situation about a different one (5.135),
* tautology and contradiction as the centre and the outer limit (5.142, 5.143).
-/

namespace Tractatus

variable {Atom : Type*}

/-- The truth of `q` follows from the truth of the propositions `ps` (in a logical space)
if every possible truth-ground common to all of `ps` is a truth-ground of `q`. -/
@[tlp "5.11"]
def FollowsFromAll (L : LogicalSpace Atom) (ps : Set (Sense Atom)) (q : Sense Atom) : Prop :=
  Set.sInter ps ∩ L.possible ⊆ q

/-- `p` follows from `q` if every possible truth-ground of `q` is a truth-ground of `p`. -/
@[tlp "5.12"]
def Follows (L : LogicalSpace Atom) (p q : Sense Atom) : Prop :=
  q ∩ L.possible ⊆ p

/-- The particular case: following from a single proposition is following from the set
consisting of it. -/
@[tlp "5.12"]
theorem followsFromAll_singleton {L : LogicalSpace Atom} {p q : Sense Atom} :
    FollowsFromAll L {q} p ↔ Follows L p q := by
  simp [FollowsFromAll, Follows]

/-- `p` follows from `q` exactly when the (possible) truth-grounds of `q` are contained in
those of `p`. -/
@[tlp "5.121"]
theorem follows_iff_subset {L : LogicalSpace Atom} {p q : Sense Atom} :
    Follows L p q ↔ q ∩ L.possible ⊆ p ∩ L.possible :=
  ⟨fun h _ hr => ⟨h hr, hr.2⟩, fun h _ hr => (h hr).1⟩

/-- The content of a proposition: the possible realities it excludes (what it says is not
the case). -/
def content (L : LogicalSpace Atom) (p : Sense Atom) : Set (Reality Atom) :=
  L.possible \ p

/-- If `p` follows from `q`, what `p` says is contained in what `q` says: the content of `p`
is part of the content of `q`. -/
@[tlp "5.122"]
theorem content_subset_of_follows {L : LogicalSpace Atom} {p q : Sense Atom}
    (h : Follows L p q) : content L p ⊆ content L q :=
  fun _ hr => ⟨hr.1, fun hq => hr.2 (h ⟨hq, hr.1⟩)⟩

/-- A proposition asserts every proposition that follows from it: wherever it is true (in
a possible reality), so is each of its consequences. -/
@[tlp "5.124"]
theorem asserts_of_follows {L : LogicalSpace Atom} {p q : Sense Atom} (h : Follows L p q)
    {r : Reality Atom} (hr : r ∈ L.possible) (hq : r ∈ q) : r ∈ p :=
  h ⟨hq, hr⟩

/-- `p . q` asserts `p` and asserts `q`. -/
@[tlp "5.1241"]
theorem follows_of_inter {L : LogicalSpace Atom} (p q : Sense Atom) :
    Follows L p (p ∩ q) ∧ Follows L q (p ∩ q) :=
  ⟨fun _ hr => hr.1.1, fun _ hr => hr.1.2⟩

/-- Two propositions are opposed if no proposition with sense (true in some possible
reality) asserts them both. -/
def Opposed (L : LogicalSpace Atom) (p q : Sense Atom) : Prop :=
  ¬ ∃ s, (s ∩ L.possible).Nonempty ∧ Follows L p s ∧ Follows L q s

/-- Two propositions are opposed exactly when they cannot be true together. -/
@[tlp "5.1241"]
theorem opposed_iff {L : LogicalSpace Atom} {p q : Sense Atom} :
    Opposed L p q ↔ p ∩ q ∩ L.possible = ∅ := by
  constructor
  · intro h
    by_contra hne
    exact h ⟨p ∩ q, Set.nonempty_iff_ne_empty.mpr hne, follows_of_inter p q⟩
  · rintro h ⟨s, ⟨r, hs, hr⟩, hp, hq⟩
    have : r ∈ p ∩ q ∩ L.possible := ⟨⟨hp ⟨hs, hr⟩, hq ⟨hs, hr⟩⟩, hr⟩
    rw [h] at this
    exact this

/-- A proposition that contradicts another denies it: the negation of the one follows from
the other. -/
@[tlp "5.1241"]
theorem follows_compl_of_opposed {L : LogicalSpace Atom} {p q : Sense Atom}
    (h : p ∩ q ∩ L.possible = ∅) : Follows L pᶜ q := by
  intro r ⟨hq, hr⟩ hp
  have : r ∈ p ∩ q ∩ L.possible := ⟨⟨hp, hq⟩, hr⟩
  rw [h] at this
  exact this

/-- Under independence, whether one truth-function of some elementary propositions follows
from another (with the same truth-arguments, standing for distinct atomic facts) can be
read off the two truth-functions alone, by checking the finitely many rows of the schema.
So it is decidable. -/
@[tlp "5.13"]
theorem follows_applyTF_iff {L : LogicalSpace Atom} (h : Independent L) {n : ℕ}
    {f g : TruthFunction n} {args : Fin n → Atom} (hinj : Function.Injective args) :
    Follows L (applyTF f args) (applyTF g args) ↔ ∀ v, g v = true → f v = true := by
  constructor
  · intro hfg v hg
    let r : Reality Atom := Function.extend args v (fun _ => false)
    have hr : (fun i => r (args i)) = v := funext fun i => hinj.extend_apply v _ i
    have : r ∈ applyTF f args := hfg ⟨by simp [applyTF, hr, hg], by rw [h]; exact Set.mem_univ _⟩
    simpa [applyTF, hr] using this
  · intro hfg r ⟨hg, _⟩
    exact hfg _ hg

/-- For example, `p` follows from `p . q`: checked by computation over the four rows. -/
@[tlp "5.13"]
theorem and_entails_left : ∀ v : Fin 2 → Bool, (v 0 && v 1) = true → v 0 = true := by
  decide

/-- Under independence, from an elementary proposition no other can be inferred: neither the
existence nor the non-existence of a different atomic fact follows from it. -/
@[tlp "5.134"]
theorem not_follows_elementary {L : LogicalSpace Atom} (h : Independent L) {a b : Atom}
    (hab : a ≠ b) : ¬ Follows L (elementary b) (elementary a) ∧
      ¬ Follows L (elementary b)ᶜ (elementary a) := by
  constructor
  · intro hf
    obtain ⟨r, hr, hra, hrb⟩ := exists_possible_of_independent h hab true false
    have := hf ⟨hra, hr⟩
    simp [elementary, hrb] at this
  · intro hf
    obtain ⟨r, hr, hra, hrb⟩ := exists_possible_of_independent h hab true true
    exact hf ⟨hra, hr⟩ hrb

/-- Under independence, from what one picture represents nothing can be inferred about a
picture of an entirely different situation (one that represents none of the same atomic
facts). -/
@[tlp "5.135"]
theorem not_follows_of_disjoint {L : LogicalSpace Atom} (h : Independent L)
    (p q : Picture Atom) (hd : ∀ a, (p.depicts a).isSome → (q.depicts a).isNone) :
    ¬ Follows L q.sense p.sense := by
  classical
  obtain ⟨a, ha⟩ := q.nontrivial
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp ha
  have hpa : p.depicts a = none := by
    cases hpa : p.depicts a with
    | none => rfl
    | some c =>
      have := hd a (by simp [hpa])
      simp [hb] at this
  let r := Function.update p.witness a (!b)
  have hr : p.IsTrue r := by
    refine (p.isTrue_congr fun x hx => ?_).mp p.witness_isTrue
    have hxa : x ≠ a := by
      rintro rfl
      simp [hpa] at hx
    simp [r, Function.update_of_ne hxa]
  intro hf
  have := hf ⟨hr, by rw [h]; exact Set.mem_univ _⟩ a b hb
  simp only [r, Function.update_self] at this
  cases b <;> simp at this

/-- If `p` follows from `q` but not conversely, then `q` says more than `p`: its content is
strictly larger. -/
@[tlp "5.14"]
theorem content_ssubset_of_follows {L : LogicalSpace Atom} {p q : Sense Atom}
    (h : Follows L p q) (h' : ¬ Follows L q p) : content L p ⊂ content L q := by
  refine ⟨content_subset_of_follows h, fun hsub => h' ?_⟩
  intro r ⟨hp, hr⟩
  by_contra hq
  exact (hsub ⟨hr, hq⟩).2 hp

/-- Under independence, if `p` and `q` follow from each other they are one and the same
proposition. -/
@[tlp "5.141"]
theorem eq_of_follows_follows {L : LogicalSpace Atom} (h : Independent L) {p q : Sense Atom}
    (hpq : Follows L p q) (hqp : Follows L q p) : p = q := by
  have hu : ∀ r, r ∈ L.possible := fun r => by rw [h]; exact Set.mem_univ _
  ext r
  exact ⟨fun hp => hqp ⟨hp, hu r⟩, fun hq => hpq ⟨hq, hu r⟩⟩

/-- A tautology follows from every proposition, and says nothing: its content is empty. -/
@[tlp "5.142"]
theorem tautology_follows {L : LogicalSpace Atom} {t : Sense Atom} (h : IsTautology t)
    (p : Sense Atom) : Follows L t p ∧ content L t = ∅ :=
  ⟨fun r _ => h r, Set.eq_empty_iff_forall_notMem.mpr fun r hr => hr.2 (h r)⟩

/-- Contradiction is the outer limit and tautology the centre: a contradiction is below every
proposition (true nowhere, so everything follows from it), a tautology above every
proposition (true wherever any proposition is). -/
@[tlp "5.143"]
theorem contradiction_bot_tautology_top {c t : Sense Atom} (hc : IsContradiction c)
    (ht : IsTautology t) (p : Sense Atom) : c ⊆ p ∧ p ⊆ t :=
  ⟨fun r hr => absurd hr (hc r), fun r _ => ht r⟩

end Tractatus
