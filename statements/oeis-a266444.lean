import Mathlib

/-!
# A266444: Middle column of the 'Rule 25' elementary cellular automaton starting with a single ON (black) cell.

Source: https://oeis.org/A266444
Credit: @snoozingnewt

The conjectures listed in the entry, all stated below as one conjunction:
* a(n) = (1-(-1)^n)/2 for n>11
* a(n) = a(n-2) for n>13
* G.f.: (1-x^2+x^4+x^9-x^10-x^11+x^13) / ((1-x)*(1+x))

Conventions (as in Wolfram's numbering and the OEIS data): the automaton runs on the integers,
starting from one ON cell at position 0 on an all-OFF background, and the rule is applied to every
cell, including the background, at each step. Offset 0: a(n) is 1 if the cell at position 0 is ON after n steps, and 0 otherwise.
The definition below reproduces every term listed in the OEIS entry.
-/

namespace OMA.S_oeis_a266444

/-- The new value of a cell under the elementary cellular automaton with Wolfram rule number
`rule`, given the old values of its left neighbour, itself and its right neighbour. -/
def ruleOut (rule : ℕ) (l c r : Bool) : Bool :=
  rule.testBit (4 * l.toNat + 2 * c.toNat + r.toNat)

/-- `cell rule t i` is the value of the cell at position `i` after `t` steps, starting from a
single ON cell at position 0. -/
def cell (rule : ℕ) : ℕ → ℤ → Bool
  | 0 => fun i => decide (i = 0)
  | t + 1 => fun i => ruleOut rule (cell rule t (i - 1)) (cell rule t i) (cell rule t (i + 1))

/-- A266444(n): 1 if the cell at position 0 is ON after n steps, and 0 otherwise. -/
def a (n : ℕ) : ℤ :=
  if cell 25 n 0 then 1 else 0

open PowerSeries in
theorem main :
    (∀ n > 11, (a n : ℚ) = ((1 - (-1 : ℚ) ^ (n : ℤ)) / 2 : ℚ)) ∧
    (∀ n > 13, a n = a (n - 2)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) * (1 + X)) = 1 - X ^ 2 + X ^ 4 + X ^ 9 - X ^ 10 - X ^ 11 + X ^ 13) := by
  sorry

end OMA.S_oeis_a266444
