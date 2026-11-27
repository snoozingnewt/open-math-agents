import Mathlib

/-!
# A266590: Decimal representation of the n-th iteration of the 'Rule 37' elementary cellular automaton starting with a single ON (black) cell.

Source: https://oeis.org/A266590
Credit: @snoozingnewt

The conjectures listed in the entry, all stated below as one conjunction:
* a(n) = 21*a(n-2)-84*a(n-4)+64*a(n-6) for n>7
* G.f.: (1+2*x-7*x^2+23*x^3-154*x^4+602*x^5+160*x^6-672*x^7) / ((1-x)*(1+x)*(1-2*x)*(1+2*x)*(1-4*x)*(1+4*x))
* a(n) = 2*4^n - 31*2^(n-2) - 1 for odd n > 1
* a(n) = 7*2^(n-1) for even n > 1

Conventions (as in Wolfram's numbering and the OEIS data): the automaton runs on the integers,
starting from one ON cell at position 0 on an all-OFF background, and the rule is applied to every
cell, including the background, at each step. Offset 0: a(n) is the cells at positions -n..n after n steps, read as the digits of a number in base 2 (leftmost cell most significant).
The definition below reproduces every term listed in the OEIS entry.
-/

namespace OMA.S_oeis_a266590

/-- The new value of a cell under the elementary cellular automaton with Wolfram rule number
`rule`, given the old values of its left neighbour, itself and its right neighbour. -/
def ruleOut (rule : ℕ) (l c r : Bool) : Bool :=
  rule.testBit (4 * l.toNat + 2 * c.toNat + r.toNat)

/-- `cell rule t i` is the value of the cell at position `i` after `t` steps, starting from a
single ON cell at position 0. -/
def cell (rule : ℕ) : ℕ → ℤ → Bool
  | 0 => fun i => decide (i = 0)
  | t + 1 => fun i => ruleOut rule (cell rule t (i - 1)) (cell rule t i) (cell rule t (i + 1))

/-- A266590(n): the cells at positions -n..n after n steps, read as the digits of a number in base 2 (leftmost cell most significant). -/
def a (n : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (2 * n + 1),
    if cell 37 n ((j : ℤ) - n) then (2 : ℤ) ^ (2 * n - j) else 0

open PowerSeries in
theorem main :
    (∀ n > 7, a n = 21 * a (n - 2) - 84 * a (n - 4) + 64 * a (n - 6)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) * (1 + X) * (1 - 2 * X) * (1 + 2 * X) * (1 - 4 * X) * (1 + 4 * X)) = 1 + 2 * X - 7 * X ^ 2 + 23 * X ^ 3 - 154 * X ^ 4 + 602 * X ^ 5 + 160 * X ^ 6 - 672 * X ^ 7) ∧
    (∀ n > 1, Odd n → (a n : ℚ) = (2 * (4 : ℚ) ^ (n : ℤ) - 31 * (2 : ℚ) ^ ((n : ℤ) - 2) - 1 : ℚ)) ∧
    (∀ n > 1, Even n → (a n : ℚ) = (7 * (2 : ℚ) ^ ((n : ℤ) - 1) : ℚ)) := by
  sorry

end OMA.S_oeis_a266590
