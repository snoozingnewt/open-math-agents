import Mathlib

/-!
# A266680: Binary representation of the middle column of the 'Rule 175' elementary cellular automaton starting with a single ON (black) cell.

Source: https://oeis.org/A266680
Credit: @snoozingnewt

The conjectures listed in the entry, all stated below as one conjunction:
* a(n) = 11*a(n-1) - 10*a(n-2) for n > 3
* G.f.: (1-x^2+x^3) / ((1-x)*(1-10*x))

Conventions (as in Wolfram's numbering and the OEIS data): the automaton runs on the integers,
starting from one ON cell at position 0 on an all-OFF background, and the rule is applied to every
cell, including the background, at each step. Offset 0: a(n) is the cells at position 0 after 0, 1, ..., n steps, read as the digits of a number in base 10 (step 0 most significant).
The definition below reproduces every term listed in the OEIS entry.
-/

namespace OMA.S_oeis_a266680

/-- The new value of a cell under the elementary cellular automaton with Wolfram rule number
`rule`, given the old values of its left neighbour, itself and its right neighbour. -/
def ruleOut (rule : ℕ) (l c r : Bool) : Bool :=
  rule.testBit (4 * l.toNat + 2 * c.toNat + r.toNat)

/-- `cell rule t i` is the value of the cell at position `i` after `t` steps, starting from a
single ON cell at position 0. -/
def cell (rule : ℕ) : ℕ → ℤ → Bool
  | 0 => fun i => decide (i = 0)
  | t + 1 => fun i => ruleOut rule (cell rule t (i - 1)) (cell rule t i) (cell rule t (i + 1))

/-- A266680(n): the cells at position 0 after 0, 1, ..., n steps, read as the digits of a number in base 10 (step 0 most significant). -/
def a (n : ℕ) : ℤ :=
  ∑ t ∈ Finset.range (n + 1), if cell 175 t 0 then (10 : ℤ) ^ (n - t) else 0

open PowerSeries in
theorem main :
    (∀ n > 3, a n = 11 * a (n - 1) - 10 * a (n - 2)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) * (1 - 10 * X)) = 1 - X ^ 2 + X ^ 3) := by
  sorry

end OMA.S_oeis_a266680
