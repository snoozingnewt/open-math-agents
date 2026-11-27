import Mathlib

/-!
# A267139: Decimal representation of the n-th iteration of the 'Rule 103' elementary cellular automaton starting with a single ON (black) cell.

Source: https://oeis.org/A267139
Credit: @snoozingnewt

The conjectures listed in the entry, all stated below as one conjunction:
* a(n) = 19*a(n-2) - 50*a(n-4) + 32*a(n-6) for n > 10
* G.f.: (1 + 6*x - 13*x^2 + 3*x^3 - 4*x^4 + 8*x^5 - 496*x^6 + 1504*x^7 - 3584*x^8 - 1536*x^9 + 4096*x^10) / ((1-x)*(1+x)*(1-4*x)*(1+4*x)*(1-2*x^2))

Conventions (as in Wolfram's numbering and the OEIS data): the automaton runs on the integers,
starting from one ON cell at position 0 on an all-OFF background, and the rule is applied to every
cell, including the background, at each step. Offset 0: a(n) is the cells at positions -n..n after n steps, read as the digits of a number in base 2 (leftmost cell most significant).
The definition below reproduces every term listed in the OEIS entry.
-/

namespace OMA.S_oeis_a267139

/-- The new value of a cell under the elementary cellular automaton with Wolfram rule number
`rule`, given the old values of its left neighbour, itself and its right neighbour. -/
def ruleOut (rule : ℕ) (l c r : Bool) : Bool :=
  rule.testBit (4 * l.toNat + 2 * c.toNat + r.toNat)

/-- `cell rule t i` is the value of the cell at position `i` after `t` steps, starting from a
single ON cell at position 0. -/
def cell (rule : ℕ) : ℕ → ℤ → Bool
  | 0 => fun i => decide (i = 0)
  | t + 1 => fun i => ruleOut rule (cell rule t (i - 1)) (cell rule t i) (cell rule t (i + 1))

/-- A267139(n): the cells at positions -n..n after n steps, read as the digits of a number in base 2 (leftmost cell most significant). -/
def a (n : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (2 * n + 1),
    if cell 103 n ((j : ℤ) - n) then (2 : ℤ) ^ (2 * n - j) else 0

open PowerSeries in
theorem main :
    (∀ n > 10, a n = 19 * a (n - 2) - 50 * a (n - 4) + 32 * a (n - 6)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) * (1 + X) * (1 - 4 * X) * (1 + 4 * X) * (1 - 2 * X ^ 2)) = 1 + 6 * X - 13 * X ^ 2 + 3 * X ^ 3 - 4 * X ^ 4 + 8 * X ^ 5 - 496 * X ^ 6 + 1504 * X ^ 7 - 3584 * X ^ 8 - 1536 * X ^ 9 + 4096 * X ^ 10) := by
  sorry

end OMA.S_oeis_a267139
