import Mathlib

/-!
# A267153: Binary representation of the n-th iteration of the 'Rule 107' elementary cellular automaton starting with a single ON (black) cell.

Source: https://oeis.org/A267153
Credit: @snoozingnewt

The conjectures listed in the entry, all stated below as one conjunction:
* a(n) = 10000*a(n-2)+a(n-4)-10000*a(n-6) for n>12
* G.f.: (1 +100*x -8989*x^2 +101110*x^3 -8999890*x^4 +99010910*x^5 -10990090000*x^6 +9900910000*x^7 -1099001110000*x^8 +989801000000*x^9 -109887911000000*x^10 +100990000000000*x^11 -11009890000000000*x^12) / ((1 -x)*(1 +x)*(1 -100*x)*(1 +100*x)*(1 +x^2))

Conventions (as in Wolfram's numbering and the OEIS data): the automaton runs on the integers,
starting from one ON cell at position 0 on an all-OFF background, and the rule is applied to every
cell, including the background, at each step. Offset 0: a(n) is the cells at positions -n..n after n steps, read as the digits of a number in base 10 (leftmost cell most significant).
The definition below reproduces every term listed in the OEIS entry.
-/

namespace OMA.S_oeis_a267153

/-- The new value of a cell under the elementary cellular automaton with Wolfram rule number
`rule`, given the old values of its left neighbour, itself and its right neighbour. -/
def ruleOut (rule : ℕ) (l c r : Bool) : Bool :=
  rule.testBit (4 * l.toNat + 2 * c.toNat + r.toNat)

/-- `cell rule t i` is the value of the cell at position `i` after `t` steps, starting from a
single ON cell at position 0. -/
def cell (rule : ℕ) : ℕ → ℤ → Bool
  | 0 => fun i => decide (i = 0)
  | t + 1 => fun i => ruleOut rule (cell rule t (i - 1)) (cell rule t i) (cell rule t (i + 1))

/-- A267153(n): the cells at positions -n..n after n steps, read as the digits of a number in base 10 (leftmost cell most significant). -/
def a (n : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (2 * n + 1),
    if cell 107 n ((j : ℤ) - n) then (10 : ℤ) ^ (2 * n - j) else 0

open PowerSeries in
theorem main :
    (∀ n > 12, a n = 10000 * a (n - 2) + a (n - 4) - 10000 * a (n - 6)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) * (1 + X) * (1 - 100 * X) * (1 + 100 * X) * (1 + X ^ 2)) = 1 + 100 * X - 8989 * X ^ 2 + 101110 * X ^ 3 - 8999890 * X ^ 4 + 99010910 * X ^ 5 - 10990090000 * X ^ 6 + 9900910000 * X ^ 7 - 1099001110000 * X ^ 8 + 989801000000 * X ^ 9 - 109887911000000 * X ^ 10 + 100990000000000 * X ^ 11 - 11009890000000000 * X ^ 12) := by
  sorry

end OMA.S_oeis_a267153
