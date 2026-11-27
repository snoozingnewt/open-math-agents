import Mathlib

/-!
# A266610: Decimal representation of the n-th iteration of the 'Rule 41' elementary cellular automaton starting with a single ON (black) cell.

Source: https://oeis.org/A266610
Credit: @snoozingnewt

The conjectures listed in the entry, all stated below as one conjunction:
* a(n) = 16*a(n-2)+a(n-4)-16*a(n-6) for n>5
* G.f.: (1-11*x^2+100*x^3-80*x^4+440*x^5) / ((1-x)*(1+x)*(1-4*x)*(1+4*x)*(1+x^2))
* a(n) = 2*4^n + 2 - 10*(n mod 4) for odd n
* a(n) = 5^((n mod 4)/2) for even n

Conventions (as in Wolfram's numbering and the OEIS data): the automaton runs on the integers,
starting from one ON cell at position 0 on an all-OFF background, and the rule is applied to every
cell, including the background, at each step. Offset 0: a(n) is the cells at positions -n..n after n steps, read as the digits of a number in base 2 (leftmost cell most significant).
The definition below reproduces every term listed in the OEIS entry.
-/

namespace OMA.S_oeis_a266610

/-- The new value of a cell under the elementary cellular automaton with Wolfram rule number
`rule`, given the old values of its left neighbour, itself and its right neighbour. -/
def ruleOut (rule : ℕ) (l c r : Bool) : Bool :=
  rule.testBit (4 * l.toNat + 2 * c.toNat + r.toNat)

/-- `cell rule t i` is the value of the cell at position `i` after `t` steps, starting from a
single ON cell at position 0. -/
def cell (rule : ℕ) : ℕ → ℤ → Bool
  | 0 => fun i => decide (i = 0)
  | t + 1 => fun i => ruleOut rule (cell rule t (i - 1)) (cell rule t i) (cell rule t (i + 1))

/-- A266610(n): the cells at positions -n..n after n steps, read as the digits of a number in base 2 (leftmost cell most significant). -/
def a (n : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (2 * n + 1),
    if cell 41 n ((j : ℤ) - n) then (2 : ℤ) ^ (2 * n - j) else 0

open PowerSeries in
theorem main :
    (∀ n > 5, a n = 16 * a (n - 2) + a (n - 4) - 16 * a (n - 6)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) * (1 + X) * (1 - 4 * X) * (1 + 4 * X) * (1 + X ^ 2)) = 1 - 11 * X ^ 2 + 100 * X ^ 3 - 80 * X ^ 4 + 440 * X ^ 5) ∧
    (∀ n : ℕ, Odd n → (a n : ℚ) = (2 * (4 : ℚ) ^ (n : ℤ) + 2 - 10 * (((n : ℤ) % 4 : ℤ) : ℚ) : ℚ)) ∧
    (∀ n : ℕ, Even n → (a n : ℚ) = ((5 : ℚ) ^ ((n : ℤ) % 4 / 2) : ℚ)) := by
  sorry

end OMA.S_oeis_a266610
