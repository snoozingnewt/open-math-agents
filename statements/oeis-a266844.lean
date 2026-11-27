import Mathlib

/-!
# A266844: Binary representation of the n-th iteration of the 'Rule 70' elementary cellular automaton starting with a single ON (black) cell.

Source: https://oeis.org/A266844
Credit: @snoozingnewt

The conjectures listed in the entry, all stated below as one conjunction:
* a(n) = (2^(n-1)*(-9*(-50)^n-2*5^n+209*50^n))/99
* a(n) = 10*a(n-1)+10000*a(n-2)-100000*a(n-3) for n>2
* G.f.: (1+100*x-1000*x^2) / ((1-10*x)*(1-100*x)*(1+100*x))

Conventions (as in Wolfram's numbering and the OEIS data): the automaton runs on the integers,
starting from one ON cell at position 0 on an all-OFF background, and the rule is applied to every
cell, including the background, at each step. Offset 0: a(n) is the cells at positions -n..n after n steps, read as the digits of a number in base 10 (leftmost cell most significant).
The definition below reproduces every term listed in the OEIS entry.
-/

namespace OMA.S_oeis_a266844

/-- The new value of a cell under the elementary cellular automaton with Wolfram rule number
`rule`, given the old values of its left neighbour, itself and its right neighbour. -/
def ruleOut (rule : ℕ) (l c r : Bool) : Bool :=
  rule.testBit (4 * l.toNat + 2 * c.toNat + r.toNat)

/-- `cell rule t i` is the value of the cell at position `i` after `t` steps, starting from a
single ON cell at position 0. -/
def cell (rule : ℕ) : ℕ → ℤ → Bool
  | 0 => fun i => decide (i = 0)
  | t + 1 => fun i => ruleOut rule (cell rule t (i - 1)) (cell rule t i) (cell rule t (i + 1))

/-- A266844(n): the cells at positions -n..n after n steps, read as the digits of a number in base 10 (leftmost cell most significant). -/
def a (n : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (2 * n + 1),
    if cell 70 n ((j : ℤ) - n) then (10 : ℤ) ^ (2 * n - j) else 0

open PowerSeries in
theorem main :
    (∀ n : ℕ, (a n : ℚ) = ((2 : ℚ) ^ ((n : ℤ) - 1) * ((-9 : ℚ) * (-50 : ℚ) ^ (n : ℤ) - 2 * (5 : ℚ) ^ (n : ℤ) + 209 * (50 : ℚ) ^ (n : ℤ)) / 99 : ℚ)) ∧
    (∀ n > 2, a n = 10 * a (n - 1) + 10000 * a (n - 2) - 100000 * a (n - 3)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - 10 * X) * (1 - 100 * X) * (1 + 100 * X)) = 1 + 100 * X - 1000 * X ^ 2) := by
  sorry

end OMA.S_oeis_a266844
