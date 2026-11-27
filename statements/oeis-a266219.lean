import Mathlib

/-!
# A266219: Binary representation of the middle column of the 'Rule 7' elementary cellular automaton starting with a single ON (black) cell.

Source: https://oeis.org/A266219
Credit: @snoozingnewt

The conjectures listed in the entry, all stated below as one conjunction:
* a(n) = 1/198*(-9*(-1)^n+109*2^(n+1)*5^n-11)
* a(n) = 10*a(n-1) + a(n-2) - 10*a(n-3) for n>2
* G.f.: (1+x-x^2) / ((1-x)*(1+x)*(1-10*x))
* a(n) = floor(109*10^n/99)

Conventions (as in Wolfram's numbering and the OEIS data): the automaton runs on the integers,
starting from one ON cell at position 0 on an all-OFF background, and the rule is applied to every
cell, including the background, at each step. Offset 0: a(n) is the cells at position 0 after 0, 1, ..., n steps, read as the digits of a number in base 10 (step 0 most significant).
The definition below reproduces every term listed in the OEIS entry.
-/

namespace OMA.S_oeis_a266219

/-- The new value of a cell under the elementary cellular automaton with Wolfram rule number
`rule`, given the old values of its left neighbour, itself and its right neighbour. -/
def ruleOut (rule : ℕ) (l c r : Bool) : Bool :=
  rule.testBit (4 * l.toNat + 2 * c.toNat + r.toNat)

/-- `cell rule t i` is the value of the cell at position `i` after `t` steps, starting from a
single ON cell at position 0. -/
def cell (rule : ℕ) : ℕ → ℤ → Bool
  | 0 => fun i => decide (i = 0)
  | t + 1 => fun i => ruleOut rule (cell rule t (i - 1)) (cell rule t i) (cell rule t (i + 1))

/-- A266219(n): the cells at position 0 after 0, 1, ..., n steps, read as the digits of a number in base 10 (step 0 most significant). -/
def a (n : ℕ) : ℤ :=
  ∑ t ∈ Finset.range (n + 1), if cell 7 t 0 then (10 : ℤ) ^ (n - t) else 0

open PowerSeries in
theorem main :
    (∀ n : ℕ, (a n : ℚ) = (1 / 198 * ((-9 : ℚ) * (-1 : ℚ) ^ (n : ℤ) + 109 * (2 : ℚ) ^ ((n : ℤ) + 1) * (5 : ℚ) ^ (n : ℤ) - 11) : ℚ)) ∧
    (∀ n > 2, a n = 10 * a (n - 1) + a (n - 2) - 10 * a (n - 3)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) * (1 + X) * (1 - 10 * X)) = 1 + X - X ^ 2) ∧
    (∀ n : ℕ, (a n : ℚ) = ((⌊(109 * (10 : ℚ) ^ (n : ℤ) / 99 : ℚ)⌋ : ℤ) : ℚ)) := by
  sorry

end OMA.S_oeis_a266219
