import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Tractatus.Consequence

/-!
# Probability (stage 3: 5.15–5.152)

With finitely many atomic facts:

* the probability that `r` gives to `s` is the number of the truth-grounds of `r` that are also
  truth-grounds of `s`, divided by the number of truth-grounds of `r` (5.15, 5.151),
* if `s` follows from `r`, the probability is 1 (5.152),
* two distinct elementary propositions give each other the probability 1/2 (5.152);
  but propositions without common truth-arguments do not in general do so (5.152 fails under
  this reading for propositions that are not elementary).
-/

namespace Tractatus

variable {Atom : Type*} [Fintype Atom] [DecidableEq Atom]

open Classical in
/-- The number of truth-grounds of a proposition. -/
noncomputable def numGrounds (p : Sense Atom) : ℕ :=
  (Finset.univ.filter (· ∈ p)).card

/-- The probability that the proposition `r` gives to the proposition `s`: the number of the
truth-grounds of `r` that are truth-grounds of `s`, divided by the number of truth-grounds of
`r`. -/
@[tlp "5.15"]
noncomputable def probGiven (r s : Sense Atom) : ℚ :=
  numGrounds (r ∩ s) / numGrounds r

open Classical in
/-- In the schema of 5.101 (the rows of `n` truth-arguments), the probability is counted on the
rows: the rows where both are true, out of the rows where `r` is true. -/
@[tlp "5.151"]
theorem probGiven_rows {n : ℕ} (f g : TruthFunction n) :
    probGiven (applyTF f id) (applyTF g id) =
      ((Finset.univ.filter fun v => f v = true ∧ g v = true).card : ℚ) /
        (Finset.univ.filter fun v => f v = true).card := by
  unfold probGiven numGrounds
  congr 3 <;> ext v <;>
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_inter_iff] <;> exact Iff.rfl

/-- If `s` follows from `r` (and `r` has truth-grounds), `r` gives `s` the probability 1. -/
@[tlp "5.152"]
theorem probGiven_of_follows {r s : Sense Atom} (hf : Follows ⟨Set.univ⟩ s r)
    (hr : numGrounds r ≠ 0) : probGiven r s = 1 := by
  have : r ∩ s = r := Set.inter_eq_left.mpr fun x hx => hf ⟨hx, Set.mem_univ x⟩
  rw [probGiven, this, div_self (by exact_mod_cast hr)]

open Classical in
theorem numGrounds_split (a b : Atom) :
    numGrounds (elementary a) =
      numGrounds (elementary a ∩ elementary b) + numGrounds (elementary a ∩ (elementary b)ᶜ) := by
  simp only [numGrounds]
  rw [← Finset.card_filter_add_card_filter_not (s := Finset.univ.filter (· ∈ elementary a))
    (p := (· ∈ elementary b))]
  simp only [Finset.filter_filter]
  congr 1 <;> congr 1 <;> ext x <;> simp

open Classical in
theorem numGrounds_flip {a b : Atom} (hab : a ≠ b) :
    numGrounds (elementary a ∩ elementary b) = numGrounds (elementary a ∩ (elementary b)ᶜ) := by
  simp only [numGrounds]
  apply Finset.card_nbij' (fun x => Function.update x b false) (fun x => Function.update x b true)
  · intro x hx
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq, elementary,
      Set.mem_inter_iff, Set.mem_compl_iff] at hx ⊢
    simp [Function.update_of_ne hab, hx.1]
  · intro x hx
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq, elementary,
      Set.mem_inter_iff, Set.mem_compl_iff] at hx ⊢
    simp [Function.update_of_ne hab, hx.1]
  · intro x hx
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq, elementary,
      Set.mem_inter_iff] at hx
    funext c
    by_cases hc : c = b
    · subst hc; simp [hx.2]
    · simp [Function.update_of_ne hc]
  · intro x hx
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq, elementary,
      Set.mem_inter_iff, Set.mem_compl_iff, Bool.not_eq_true] at hx
    funext c
    by_cases hc : c = b
    · subst hc; simp [hx.2]
    · simp [Function.update_of_ne hc]

/-- Two distinct elementary propositions give each other the probability 1/2. -/
@[tlp "5.152"]
theorem probGiven_elementary {a b : Atom} (hab : a ≠ b) :
    probGiven (elementary a) (elementary b) = 1 / 2 := by
  classical
  have hpos : numGrounds (elementary a ∩ elementary b) ≠ 0 := by
    simp only [numGrounds, ne_eq, Finset.card_eq_zero, Finset.filter_eq_empty_iff, not_forall,
      not_not]
    exact ⟨fun _ => true, Finset.mem_univ _, rfl, rfl⟩
  rw [probGiven, numGrounds_split a b, ← numGrounds_flip hab]
  have : (numGrounds (elementary a ∩ elementary b) : ℚ) ≠ 0 := by exact_mod_cast hpos
  push_cast
  field_simp
  ring

open Classical in
/-- Propositions without common truth-arguments do not in general give each other the
probability 1/2: with three atomic facts, `p` (an elementary proposition of the first) gives
`q ∨ r` (of the other two) the probability 3/4. So the claim of 5.152 holds for elementary
propositions, but not for independent propositions in general. -/
@[tlp_refutes "5.152"]
theorem independent_not_half :
    probGiven (elementary (0 : Fin 3)) (elementary 1 ∪ elementary 2) = 3 / 4 ∧
      probGiven (elementary (0 : Fin 3)) (elementary 1 ∪ elementary 2) ≠ 1 / 2 := by
  have h1 : numGrounds (elementary (0 : Fin 3) ∩ (elementary 1 ∪ elementary 2)) = 3 := by
    simp only [numGrounds]
    convert (show (Finset.univ.filter (fun x : Fin 3 → Bool =>
        x 0 = true ∧ (x 1 = true ∨ x 2 = true))).card = 3 by decide) using 2
    ext x; simp [elementary]
  have h2 : numGrounds (elementary (0 : Fin 3)) = 4 := by
    simp only [numGrounds]
    convert (show (Finset.univ.filter (fun x : Fin 3 → Bool => x 0 = true)).card = 4 by
      decide) using 2
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rfl
  rw [probGiven, h1, h2]
  norm_num

end Tractatus
