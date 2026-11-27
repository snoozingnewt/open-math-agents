import Mathlib

/-!
# A267293: Binary representation of the n-th iteration of the 'Rule 121' elementary cellular automaton starting with a single ON (black) cell.

Source: https://oeis.org/A267293
Credit: @snoozingnewt

The conjectures listed in the entry, all stated below as one conjunction:
* a(n) = a(n-2)+100000000*a(n-4)-100000000*a(n-6) for n>12
* G.f.: (1 +x +11009*x^2 +111010*x^3 +11000090*x^4 +910990100*x^5 +90098900*x^6 +9099010000*x^7 -1109990110000*x^8 +979901000000*x^9 -108789011000000*x^10 -989900000000*x^11 +109898900000000*x^12) / ((1 -x)*(1 +x)*(1 -100*x)*(1 +100*x)*(1 +10000*x^2))

Conventions (as in Wolfram's numbering and the OEIS data): the automaton runs on the integers,
starting from one ON cell at position 0 on an all-OFF background, and the rule is applied to every
cell, including the background, at each step. Offset 0: a(n) is the cells at positions -n..n after n steps, read as the digits of a number in base 10 (leftmost cell most significant).
The definition below reproduces every term listed in the OEIS entry.
-/

namespace OMA.S_oeis_a267293

/-- The new value of a cell under the elementary cellular automaton with Wolfram rule number
`rule`, given the old values of its left neighbour, itself and its right neighbour. -/
def ruleOut (rule : ℕ) (l c r : Bool) : Bool :=
  rule.testBit (4 * l.toNat + 2 * c.toNat + r.toNat)

/-- `cell rule t i` is the value of the cell at position `i` after `t` steps, starting from a
single ON cell at position 0. -/
def cell (rule : ℕ) : ℕ → ℤ → Bool
  | 0 => fun i => decide (i = 0)
  | t + 1 => fun i => ruleOut rule (cell rule t (i - 1)) (cell rule t i) (cell rule t (i + 1))

/-- A267293(n): the cells at positions -n..n after n steps, read as the digits of a number in base 10 (leftmost cell most significant). -/
def a (n : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (2 * n + 1),
    if cell 121 n ((j : ℤ) - n) then (10 : ℤ) ^ (2 * n - j) else 0

open PowerSeries in
theorem main :
    (∀ n > 12, a n = a (n - 2) + 100000000 * a (n - 4) - 100000000 * a (n - 6)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) * (1 + X) * (1 - 100 * X) * (1 + 100 * X) * (1 + 10000 * X ^ 2)) = 1 + X + 11009 * X ^ 2 + 111010 * X ^ 3 + 11000090 * X ^ 4 + 910990100 * X ^ 5 + 90098900 * X ^ 6 + 9099010000 * X ^ 7 - 1109990110000 * X ^ 8 + 979901000000 * X ^ 9 - 108789011000000 * X ^ 10 - 989900000000 * X ^ 11 + 109898900000000 * X ^ 12) := by
  sorry

end OMA.S_oeis_a267293
