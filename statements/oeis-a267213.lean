import Mathlib

/-!
# A267213: Number of OFF (white) cells in the n-th iteration of the 'Rule 109' elementary cellular automaton starting with a single ON (black) cell.

Source: https://oeis.org/A267213
Credit: @snoozingnewt

The conjectures listed in the entry, all stated below as one conjunction:
* a(n) = a(n-3)+a(n-4)-a(n-7) for n>7
* G.f.: x*(2+5*x^2+2*x^4-2*x^5+3*x^6) / ((1-x)^2*(1+x)*(1+x^2)*(1+x+x^2))

Conventions (as in Wolfram's numbering and the OEIS data): the automaton runs on the integers,
starting from one ON cell at position 0 on an all-OFF background, and the rule is applied to every
cell, including the background, at each step. Offset 0: a(n) is the number of OFF cells among positions -n..n after n steps.
The definition below reproduces every term listed in the OEIS entry.
-/

namespace OMA.S_oeis_a267213

/-- The new value of a cell under the elementary cellular automaton with Wolfram rule number
`rule`, given the old values of its left neighbour, itself and its right neighbour. -/
def ruleOut (rule : ℕ) (l c r : Bool) : Bool :=
  rule.testBit (4 * l.toNat + 2 * c.toNat + r.toNat)

/-- `cell rule t i` is the value of the cell at position `i` after `t` steps, starting from a
single ON cell at position 0. -/
def cell (rule : ℕ) : ℕ → ℤ → Bool
  | 0 => fun i => decide (i = 0)
  | t + 1 => fun i => ruleOut rule (cell rule t (i - 1)) (cell rule t i) (cell rule t (i + 1))

/-- A267213(n): the number of OFF cells among positions -n..n after n steps. -/
def a (n : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (2 * n + 1), if cell 109 n ((j : ℤ) - n) then 0 else 1

open PowerSeries in
theorem main :
    (∀ n > 7, a n = a (n - 3) + a (n - 4) - a (n - 7)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) ^ 2 * (1 + X) * (1 + X ^ 2) * (1 + X + X ^ 2)) = X * (2 + 5 * X ^ 2 + 2 * X ^ 4 - 2 * X ^ 5 + 3 * X ^ 6)) := by
  sorry

end OMA.S_oeis_a267213
