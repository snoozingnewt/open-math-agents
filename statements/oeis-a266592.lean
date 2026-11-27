import Mathlib

/-!
# A266592: Binary representation of the middle column of the 'Rule 37' elementary cellular automaton starting with a single ON (black) cell.

Source: https://oeis.org/A266592
Credit: @snoozingnewt

The conjectures listed in the entry, all stated below as one conjunction:
* a(n) = (45*(-1)^n+1099*10^n-55)/990 for n>0
* a(n) = 10*a(n-1)+a(n-2)-10*a(n-3) for n>3
* G.f.: (1+x-x^3) / ((1-x)*(1+x)*(1-10*x))

Conventions (as in Wolfram's numbering and the OEIS data): the automaton runs on the integers,
starting from one ON cell at position 0 on an all-OFF background, and the rule is applied to every
cell, including the background, at each step. Offset 0: a(n) is the cells at position 0 after 0, 1, ..., n steps, read as the digits of a number in base 10 (step 0 most significant).
The definition below reproduces every term listed in the OEIS entry.
-/

namespace OMA.S_oeis_a266592

/-- The new value of a cell under the elementary cellular automaton with Wolfram rule number
`rule`, given the old values of its left neighbour, itself and its right neighbour. -/
def ruleOut (rule : ℕ) (l c r : Bool) : Bool :=
  rule.testBit (4 * l.toNat + 2 * c.toNat + r.toNat)

/-- `cell rule t i` is the value of the cell at position `i` after `t` steps, starting from a
single ON cell at position 0. -/
def cell (rule : ℕ) : ℕ → ℤ → Bool
  | 0 => fun i => decide (i = 0)
  | t + 1 => fun i => ruleOut rule (cell rule t (i - 1)) (cell rule t i) (cell rule t (i + 1))

/-- A266592(n): the cells at position 0 after 0, 1, ..., n steps, read as the digits of a number in base 10 (step 0 most significant). -/
def a (n : ℕ) : ℤ :=
  ∑ t ∈ Finset.range (n + 1), if cell 37 t 0 then (10 : ℤ) ^ (n - t) else 0

open PowerSeries in
theorem main :
    (∀ n > 0, (a n : ℚ) = ((45 * (-1 : ℚ) ^ (n : ℤ) + 1099 * (10 : ℚ) ^ (n : ℤ) - 55) / 990 : ℚ)) ∧
    (∀ n > 3, a n = 10 * a (n - 1) + a (n - 2) - 10 * a (n - 3)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) * (1 + X) * (1 - 10 * X)) = 1 + X - X ^ 3) := by
  sorry

end OMA.S_oeis_a266592
