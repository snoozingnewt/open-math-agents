import Mathlib

/-!
# A266787: Binary representation of the n-th iteration of the 'Rule 61' elementary cellular automaton starting with a single ON (black) cell.

Source: https://oeis.org/A266787
Credit: @snoozingnewt

The conjectures listed in the entry, all stated below as one conjunction:
* a(n) = 11001*a(n-2)-10011000*a(n-4)+10000000*a(n-6) for n>10
* G.f.: (1 +11*x -9901*x^2 +889100*x^3 -979100*x^4 +7891000*x^5 -109001000*x^6 +1090110000*x^7 +9990000*x^8 -1100000000*x^9 +100000000*x^10) / ((1 -x)*(1 +x)*(1 -100*x)*(1 +100*x)*(1 -1000*x^2))

Conventions (as in Wolfram's numbering and the OEIS data): the automaton runs on the integers,
starting from one ON cell at position 0 on an all-OFF background, and the rule is applied to every
cell, including the background, at each step. Offset 0: a(n) is the cells at positions -n..n after n steps, read as the digits of a number in base 10 (leftmost cell most significant).
The definition below reproduces every term listed in the OEIS entry.
-/

namespace OMA.S_oeis_a266787

/-- The new value of a cell under the elementary cellular automaton with Wolfram rule number
`rule`, given the old values of its left neighbour, itself and its right neighbour. -/
def ruleOut (rule : ℕ) (l c r : Bool) : Bool :=
  rule.testBit (4 * l.toNat + 2 * c.toNat + r.toNat)

/-- `cell rule t i` is the value of the cell at position `i` after `t` steps, starting from a
single ON cell at position 0. -/
def cell (rule : ℕ) : ℕ → ℤ → Bool
  | 0 => fun i => decide (i = 0)
  | t + 1 => fun i => ruleOut rule (cell rule t (i - 1)) (cell rule t i) (cell rule t (i + 1))

/-- A266787(n): the cells at positions -n..n after n steps, read as the digits of a number in base 10 (leftmost cell most significant). -/
def a (n : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (2 * n + 1),
    if cell 61 n ((j : ℤ) - n) then (10 : ℤ) ^ (2 * n - j) else 0

open PowerSeries in
theorem main :
    (∀ n > 10, a n = 11001 * a (n - 2) - 10011000 * a (n - 4) + 10000000 * a (n - 6)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) * (1 + X) * (1 - 100 * X) * (1 + 100 * X) * (1 - 1000 * X ^ 2)) = 1 + 11 * X - 9901 * X ^ 2 + 889100 * X ^ 3 - 979100 * X ^ 4 + 7891000 * X ^ 5 - 109001000 * X ^ 6 + 1090110000 * X ^ 7 + 9990000 * X ^ 8 - 1100000000 * X ^ 9 + 100000000 * X ^ 10) := by
  sorry

end OMA.S_oeis_a266787
