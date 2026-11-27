import Mathlib

/-!
# A267294: Decimal representation of the n-th iteration of the 'Rule 121' elementary cellular automaton starting with a single ON (black) cell.

Source: https://oeis.org/A267294
Credit: @snoozingnewt

The conjectures listed in the entry, all stated below as one conjunction:
* a(n) = a(n-2)+256*a(n-4)-256*a(n-6) for n>12
* G.f.: (1 +x +25*x^2 +58*x^3 +194*x^4 +436*x^5 +148*x^6 +720*x^7 -7088*x^8 +1856*x^9 -15040*x^10 -2816*x^11 +21760*x^12) / ((1-x)*(1+x)*(1-4*x)*(1+4*x)*(1+16*x^2))

Conventions (as in Wolfram's numbering and the OEIS data): the automaton runs on the integers,
starting from one ON cell at position 0 on an all-OFF background, and the rule is applied to every
cell, including the background, at each step. Offset 0: a(n) is the cells at positions -n..n after n steps, read as the digits of a number in base 2 (leftmost cell most significant).
The definition below reproduces every term listed in the OEIS entry.
-/

namespace OMA.S_oeis_a267294

/-- The new value of a cell under the elementary cellular automaton with Wolfram rule number
`rule`, given the old values of its left neighbour, itself and its right neighbour. -/
def ruleOut (rule : ℕ) (l c r : Bool) : Bool :=
  rule.testBit (4 * l.toNat + 2 * c.toNat + r.toNat)

/-- `cell rule t i` is the value of the cell at position `i` after `t` steps, starting from a
single ON cell at position 0. -/
def cell (rule : ℕ) : ℕ → ℤ → Bool
  | 0 => fun i => decide (i = 0)
  | t + 1 => fun i => ruleOut rule (cell rule t (i - 1)) (cell rule t i) (cell rule t (i + 1))

/-- A267294(n): the cells at positions -n..n after n steps, read as the digits of a number in base 2 (leftmost cell most significant). -/
def a (n : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (2 * n + 1),
    if cell 121 n ((j : ℤ) - n) then (2 : ℤ) ^ (2 * n - j) else 0

open PowerSeries in
theorem main :
    (∀ n > 12, a n = a (n - 2) + 256 * a (n - 4) - 256 * a (n - 6)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) * (1 + X) * (1 - 4 * X) * (1 + 4 * X) * (1 + 16 * X ^ 2)) = 1 + X + 25 * X ^ 2 + 58 * X ^ 3 + 194 * X ^ 4 + 436 * X ^ 5 + 148 * X ^ 6 + 720 * X ^ 7 - 7088 * X ^ 8 + 1856 * X ^ 9 - 15040 * X ^ 10 - 2816 * X ^ 11 + 21760 * X ^ 12) := by
  sorry

end OMA.S_oeis_a267294
