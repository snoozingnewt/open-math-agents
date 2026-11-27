import Mathlib

/-!
# A267678: Decimal representation of the n-th iteration of the 'Rule 197' elementary cellular automaton starting with a single ON (black) cell.

Source: https://oeis.org/A267678
Credit: @snoozingnewt

The conjectures listed in the entry, all stated below as one conjunction:
* a(n) = 6*a(n-1)-7*a(n-2)-6*a(n-3)+8*a(n-4) for n>5
* G.f.: (1-4*x+15*x^2+4*x^3-12*x^4-16*x^5) / ((1-x)*(1+x)*(1-2*x)*(1-4*x))
* a(n) = 2*(-3 + (-1)^n - 2^(2+n) + 3*4^n)/3 for n>1
* a(n) = floor((6*4^n - 8*2^n)/3) - 2^(n mod 2) for n > 1

Conventions (as in Wolfram's numbering and the OEIS data): the automaton runs on the integers,
starting from one ON cell at position 0 on an all-OFF background, and the rule is applied to every
cell, including the background, at each step. Offset 0: a(n) is the cells at positions -n..n after n steps, read as the digits of a number in base 2 (leftmost cell most significant).
The definition below reproduces every term listed in the OEIS entry.
-/

namespace OMA.S_oeis_a267678

/-- The new value of a cell under the elementary cellular automaton with Wolfram rule number
`rule`, given the old values of its left neighbour, itself and its right neighbour. -/
def ruleOut (rule : ℕ) (l c r : Bool) : Bool :=
  rule.testBit (4 * l.toNat + 2 * c.toNat + r.toNat)

/-- `cell rule t i` is the value of the cell at position `i` after `t` steps, starting from a
single ON cell at position 0. -/
def cell (rule : ℕ) : ℕ → ℤ → Bool
  | 0 => fun i => decide (i = 0)
  | t + 1 => fun i => ruleOut rule (cell rule t (i - 1)) (cell rule t i) (cell rule t (i + 1))

/-- A267678(n): the cells at positions -n..n after n steps, read as the digits of a number in base 2 (leftmost cell most significant). -/
def a (n : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (2 * n + 1),
    if cell 197 n ((j : ℤ) - n) then (2 : ℤ) ^ (2 * n - j) else 0

open PowerSeries in
theorem main :
    (∀ n > 5, a n = 6 * a (n - 1) - 7 * a (n - 2) - 6 * a (n - 3) + 8 * a (n - 4)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) * (1 + X) * (1 - 2 * X) * (1 - 4 * X)) = 1 - 4 * X + 15 * X ^ 2 + 4 * X ^ 3 - 12 * X ^ 4 - 16 * X ^ 5) ∧
    (∀ n > 1, (a n : ℚ) = (2 * ((-3 : ℚ) + (-1 : ℚ) ^ (n : ℤ) - (2 : ℚ) ^ (2 + (n : ℤ)) + 3 * (4 : ℚ) ^ (n : ℤ)) / 3 : ℚ)) ∧
    (∀ n > 1, (a n : ℚ) = (((⌊((6 * (4 : ℚ) ^ (n : ℤ) - 8 * (2 : ℚ) ^ (n : ℤ)) / 3 : ℚ)⌋ : ℤ) : ℚ) - (2 : ℚ) ^ ((n : ℤ) % 2) : ℚ)) := by
  sorry

end OMA.S_oeis_a267678
