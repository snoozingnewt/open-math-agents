import Mathlib

/-!
# A266589: Binary representation of the n-th iteration of the 'Rule 37' elementary cellular automaton starting with a single ON (black) cell.

Source: https://oeis.org/A266589
Credit: @snoozingnewt

The conjectures listed in the entry, all stated below as one conjunction:
* a(n) = 10101*a(n-2)-1010100*a(n-4)+1000000*a(n-6) for n>7
* G.f.: (1 +10*x -8991*x^2 +898991*x^3 -10091010*x^4 +1009091010*x^5 +10100000*x^6 -1010100000*x^7) / ((1 -x)*(1 +x)*(1 -10*x)*(1 +10*x)*(1 -100*x)*(1 +100*x))
* a(n) = (10*100^n - 99999*10^(n-2) - 1)/9 for odd n > 1
* a(n) = 111*10^(n-1) for even n > 1

Conventions (as in Wolfram's numbering and the OEIS data): the automaton runs on the integers,
starting from one ON cell at position 0 on an all-OFF background, and the rule is applied to every
cell, including the background, at each step. Offset 0: a(n) is the cells at positions -n..n after n steps, read as the digits of a number in base 10 (leftmost cell most significant).
The definition below reproduces every term listed in the OEIS entry.
-/

namespace OMA.S_oeis_a266589

/-- The new value of a cell under the elementary cellular automaton with Wolfram rule number
`rule`, given the old values of its left neighbour, itself and its right neighbour. -/
def ruleOut (rule : ℕ) (l c r : Bool) : Bool :=
  rule.testBit (4 * l.toNat + 2 * c.toNat + r.toNat)

/-- `cell rule t i` is the value of the cell at position `i` after `t` steps, starting from a
single ON cell at position 0. -/
def cell (rule : ℕ) : ℕ → ℤ → Bool
  | 0 => fun i => decide (i = 0)
  | t + 1 => fun i => ruleOut rule (cell rule t (i - 1)) (cell rule t i) (cell rule t (i + 1))

/-- A266589(n): the cells at positions -n..n after n steps, read as the digits of a number in base 10 (leftmost cell most significant). -/
def a (n : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (2 * n + 1),
    if cell 37 n ((j : ℤ) - n) then (10 : ℤ) ^ (2 * n - j) else 0

open PowerSeries in
theorem main :
    (∀ n > 7, a n = 10101 * a (n - 2) - 1010100 * a (n - 4) + 1000000 * a (n - 6)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) * (1 + X) * (1 - 10 * X) * (1 + 10 * X) * (1 - 100 * X) * (1 + 100 * X)) = 1 + 10 * X - 8991 * X ^ 2 + 898991 * X ^ 3 - 10091010 * X ^ 4 + 1009091010 * X ^ 5 + 10100000 * X ^ 6 - 1010100000 * X ^ 7) ∧
    (∀ n > 1, Odd n → (a n : ℚ) = ((10 * (100 : ℚ) ^ (n : ℤ) - 99999 * (10 : ℚ) ^ ((n : ℤ) - 2) - 1) / 9 : ℚ)) ∧
    (∀ n > 1, Even n → (a n : ℚ) = (111 * (10 : ℚ) ^ ((n : ℤ) - 1) : ℚ)) := by
  sorry

end OMA.S_oeis_a266589
