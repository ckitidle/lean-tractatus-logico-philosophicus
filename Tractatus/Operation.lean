import Mathlib.Logic.Function.Iterate
import Mathlib.Order.SetNotation
import Mathlib.Data.Set.Basic
import Tractatus.Meta

/-!
# Operations, formal series and numbers (stage 2: 4.1252, 4.1273, 5.22–5.2523, 6.02–6.03,
6.241)

* an operation turns a proposition (or anything of a given kind) into another of the same
  kind, so its result can be its own base (5.22, 5.23, 5.251),
* successive application of an operation (5.2521) and the formal series
  `[a, x, O'x]` it generates (5.2522, 4.1252),
* the formal series coincides with what Frege's definition of "successor" picks out: the
  members of every class containing `a` and closed under `O` (4.1273, 5.232, 5.2523),
* a number is the exponent of an operation (6.02, 6.021), the general form of the cardinal
  number `[0, ξ, ξ + 1]` (6.03), and the calculation of 6.241 (`2 × 2 = 4`).

The numbers used as exponents are Lean's natural numbers; the *Tractatus* defines numbers
from operations instead (recorded in correspondence/stage2.md).
-/

namespace Tractatus

variable {α : Type*}

/-- An operation: what must be done to something (a proposition) to make another of the same
kind out of it, represented by a map from that kind to itself. -/
@[tlp "5.22", tlp "5.23"]
abbrev Operation (α : Type*) := α → α

/-- The successive application of an operation: `successive O n a` is the result of applying
`O` to `a`, then to the result, and so on, `n` times (`O'O'O'a` for `n = 3`). The number `n`
is the exponent of the operation. -/
@[tlp "5.2521", tlp "6.02", tlp "6.021"]
def successive (O : Operation α) (n : ℕ) (a : α) : α :=
  O^[n] a

/-- The definitions of 6.02: `x = Ω⁰'x` and `Ω'Ω^ν'x = Ω^(ν+1)'x`. -/
@[tlp "6.02"]
theorem successive_zero (O : Operation α) (a : α) : successive O 0 a = a :=
  rfl

/-- The same operation makes each term of the series from the previous one, and its result
is again a base for it: `Ω'Ω^ν'x = Ω^(ν+1)'x`. -/
@[tlp "6.02", tlp "5.242", tlp "5.251"]
theorem successive_succ (O : Operation α) (n : ℕ) (a : α) :
    O (successive O n a) = successive O (n + 1) a :=
  (Function.iterate_succ_apply' O n a).symm

/-- The formal series `[a, x, O'x]`: the terms obtained from the first term `a` by
successive application of `O`. The series is ordered by the operation, an internal
relation. -/
@[tlp "5.2522", tlp "4.1252"]
def formalSeries (a : α) (O : Operation α) : Set α :=
  {b | ∃ n, successive O n a = b}

/-- Frege's way of saying that `b` follows `a` in the series: `b` belongs to every class that
contains `a` and is closed under `O`. -/
def ancestral (a : α) (O : Operation α) : Set α :=
  {b | ∀ S : Set α, a ∈ S → (∀ x ∈ S, O x ∈ S) → b ∈ S}

/-- The formal series `[a, x, O'x]` contains exactly what Frege's definition picks out: the
successive application of an operation ("and so on") and the internal relation ordering the
series come to the same terms. -/
@[tlp "4.1273", tlp "5.232", tlp "5.2523"]
theorem formalSeries_eq_ancestral (a : α) (O : Operation α) :
    formalSeries a O = ancestral a O := by
  ext b
  constructor
  · rintro ⟨n, rfl⟩ S ha hS
    induction n with
    | zero => exact ha
    | succ n ih => rw [← successive_succ]; exact hS _ ih
  · intro h
    refine h (formalSeries a O) ⟨0, rfl⟩ ?_
    rintro x ⟨n, rfl⟩
    exact ⟨n + 1, (successive_succ O n a).symm⟩

/-- The general form of the cardinal number `[0, ξ, ξ + 1]`: the formal series generated from
`0` by adding one. -/
@[tlp "6.03"]
def cardinalSeries : Set ℕ :=
  formalSeries 0 Nat.succ

/-- Every natural number is a term of the series `[0, ξ, ξ + 1]`. -/
@[tlp "6.03"]
theorem cardinalSeries_eq_univ : cardinalSeries = Set.univ := by
  refine Set.eq_univ_of_forall fun n => ⟨n, ?_⟩
  induction n with
  | zero => rfl
  | succ n ih => rw [← successive_succ, ih]

/-- The rule used in 6.241: `(Ω^ν)^μ'x = Ω^(ν×μ)'x`. -/
@[tlp "6.241"]
theorem successive_successive (O : Operation α) (ν μ : ℕ) (a : α) :
    successive (successive O ν) μ a = successive O (ν * μ) a := by
  have : successive O ν = O^[ν] := rfl
  simp only [successive, this]
  rw [Function.iterate_mul]

/-- The calculation of 6.241: `(Ω²)²'x = Ω^(2×2)'x = Ω⁴'x`, step by step through
`Ω²'Ω²'x = Ω^(2+2)'x`. -/
@[tlp "6.241"]
theorem two_times_two (O : Operation α) (a : α) :
    successive (successive O 2) 2 a = successive O 4 a ∧
      successive O 2 (successive O 2 a) = successive O (2 + 2) a := by
  refine ⟨successive_successive O 2 2 a, ?_⟩
  simp only [successive]
  rw [← Function.iterate_add_apply]

end Tractatus
