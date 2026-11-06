import Mathlib
open Finset
/-You have a $10 \times 10$ grid of squares. You write a number in each square as follows: you write $1,2,3, \ldots, 10$ from left to right across the top row, then $11,12, \ldots, 20$ across the second row, and so on, ending with a 100 in the bottom right square. You then write a second number in each square, writing $1,2, \ldots, 10$ in the first column (from top to bottom), then $11,12, \ldots, 20$ in the second column, and so forth.

When this process is finished, how many squares will have the property that their two numbers sum to 101 ?-/
theorem number_theory_611222 :
  let positions := (((Icc 1 10).product (Icc 1 10)).filter (λ p => 10 * (p.1 - 1) + p.2 + 10 * (p.2 - 1) + p.1 = 101))
  positions.card = 10 := by
  decide