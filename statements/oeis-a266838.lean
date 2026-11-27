import Mathlib

/-!
# A266838: Binary representation of the n-th iteration of the 'Rule 67' elementary cellular automaton starting with a single ON (black) cell.

Source: https://oeis.org/A266838
Credit: @snoozingnewt

The conjectures listed in the entry, all stated below as one conjunction:
* a(n) = 11001*a(n-2) - 10011000*a(n-4) + 10000000*a(n-6) for n > 9
* G.f.: (1 + 100*x - 9991*x^2 - 99*x^3 - 88910*x^4 - 9990*x^5 - 10901100*x^6 - 99900*x^7 + 11000000*x^8 - 1000000*x^9) / ((1-x)*(1+x)*(1-100*x)*(1+100*x)*(1-1000*x^2))
* a(n) = (10*100^n - 999909*1000^floor(n/2)/10000 - 1)/9 for odd n > 3
* a(n) = 10111*1000^(n/2)/10000 for even n > 3

Conventions (as in Wolfram's numbering and the OEIS data): the automaton runs on the integers,
starting from one ON cell at position 0 on an all-OFF background, and the rule is applied to every
cell, including the background, at each step. Offset 0: a(n) is the cells at positions -n..n after n steps, read as the digits of a number in base 10 (leftmost cell most significant).
The definition below reproduces every term listed in the OEIS entry.
-/

namespace OMA.S_oeis_a266838

/-- The new value of a cell under the elementary cellular automaton with Wolfram rule number
`rule`, given the old values of its left neighbour, itself and its right neighbour. -/
def ruleOut (rule : ℕ) (l c r : Bool) : Bool :=
  rule.testBit (4 * l.toNat + 2 * c.toNat + r.toNat)

/-- `cell rule t i` is the value of the cell at position `i` after `t` steps, starting from a
single ON cell at position 0. -/
def cell (rule : ℕ) : ℕ → ℤ → Bool
  | 0 => fun i => decide (i = 0)
  | t + 1 => fun i => ruleOut rule (cell rule t (i - 1)) (cell rule t i) (cell rule t (i + 1))

/-- A266838(n): the cells at positions -n..n after n steps, read as the digits of a number in base 10 (leftmost cell most significant). -/
def a (n : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (2 * n + 1),
    if cell 67 n ((j : ℤ) - n) then (10 : ℤ) ^ (2 * n - j) else 0

open PowerSeries in
theorem main :
    (∀ n > 9, a n = 11001 * a (n - 2) - 10011000 * a (n - 4) + 10000000 * a (n - 6)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) * (1 + X) * (1 - 100 * X) * (1 + 100 * X) * (1 - 1000 * X ^ 2)) = 1 + 100 * X - 9991 * X ^ 2 - 99 * X ^ 3 - 88910 * X ^ 4 - 9990 * X ^ 5 - 10901100 * X ^ 6 - 99900 * X ^ 7 + 11000000 * X ^ 8 - 1000000 * X ^ 9) ∧
    (∀ n > 3, Odd n → (a n : ℚ) = ((10 * (100 : ℚ) ^ (n : ℤ) - 999909 * (1000 : ℚ) ^ ((n : ℤ) / 2) / 10000 - 1) / 9 : ℚ)) ∧
    (∀ n > 3, Even n → (a n : ℚ) = (10111 * (1000 : ℚ) ^ ((n : ℤ) / 2) / 10000 : ℚ)) := by
  sorry

end OMA.S_oeis_a266838
