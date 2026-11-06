import Mathlib
open Real


theorem algebra_94581 (x y : ℝ) (h : abs (x + y) + abs (x - y) = 2) :
x ^ 2 - 6 * x + y ^ 2 ≤ 8 := by
  cases' abs_cases (x + y) with h1 h1 <;> 
    cases' abs_cases (x - y) with h2 h2 <;> 
      nlinarith [sq_nonneg (x + 1), sq_nonneg (y - 1), sq_nonneg (y + 1), sq_nonneg (x - 1)]