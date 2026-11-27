import Mathlib

/-!
# A266252: Total number of OFF (white) cells after n iterations of the 'Rule 9' elementary cellular automaton starting with a single ON (black) cell.

Source: https://oeis.org/A266252
Credit: @snoozingnewt

The conjectures listed in the entry, all stated below as one conjunction:
* a(n) = ((-1)^n*(n-4)+n*(n+4))/2 for n>2
* a(n) = a(n-1)+2*a(n-2)-2*a(n-3)-a(n-4)+a(n-5) for n>7
* G.f.: x*(3+3*x-x^2-x^3-x^4+2*x^5-x^6) / ((1-x)^3*(1+x)^2)

Conventions (as in Wolfram's numbering and the OEIS data): the automaton runs on the integers,
starting from one ON cell at position 0 on an all-OFF background, and the rule is applied to every
cell, including the background, at each step. Offset 0: a(n) is the total number of OFF cells among positions -t..t after t steps, summed over t = 0..n.
The definition below reproduces every term listed in the OEIS entry.
-/

namespace OMA.S_oeis_a266252

/-- The new value of a cell under the elementary cellular automaton with Wolfram rule number
`rule`, given the old values of its left neighbour, itself and its right neighbour. -/
def ruleOut (rule : ℕ) (l c r : Bool) : Bool :=
  rule.testBit (4 * l.toNat + 2 * c.toNat + r.toNat)

/-- `cell rule t i` is the value of the cell at position `i` after `t` steps, starting from a
single ON cell at position 0. -/
def cell (rule : ℕ) : ℕ → ℤ → Bool
  | 0 => fun i => decide (i = 0)
  | t + 1 => fun i => ruleOut rule (cell rule t (i - 1)) (cell rule t i) (cell rule t (i + 1))

/-- A266252(n): the total number of OFF cells among positions -t..t after t steps, summed over t = 0..n. -/
def a (n : ℕ) : ℤ :=
  ∑ t ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (2 * t + 1),
    if cell 9 t ((j : ℤ) - t) then 0 else 1

open PowerSeries in
theorem main :
    (∀ n > 2, (a n : ℚ) = (((-1 : ℚ) ^ (n : ℤ) * ((n : ℚ) - 4) + (n : ℚ) * ((n : ℚ) + 4)) / 2 : ℚ)) ∧
    (∀ n > 7, a n = a (n - 1) + 2 * a (n - 2) - 2 * a (n - 3) - a (n - 4) + a (n - 5)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) ^ 3 * (1 + X) ^ 2) = X * (3 + 3 * X - X ^ 2 - X ^ 3 - X ^ 4 + 2 * X ^ 5 - X ^ 6)) := by
  sorry

end OMA.S_oeis_a266252
