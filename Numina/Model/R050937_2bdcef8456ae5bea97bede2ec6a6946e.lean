import Mathlib

theorem algebra_12539 {x : ℤ} (h : x * (x + 1) * (x + 2) = 210) : x + (x + 1) + (x + 2) = 18 := by 
  have eq2 : x ≤ 14 := by
    nlinarith [sq_nonneg (x * (x + 1)), sq_nonneg (x + 1), sq_nonneg (x), sq_nonneg (x + 2), sq_nonneg (x * (x + 2)), sq_nonneg ((x) * (x + 1) * (x + 2)), sq_nonneg (x - 5), sq_nonneg (x + 6), sq_nonneg (x + 5)]
  have eq3 : x ≥ -15 := by
    nlinarith [sq_nonneg (x * (x + 1)), sq_nonneg (x + 1), sq_nonneg (x), sq_nonneg (x + 2), sq_nonneg (x * (x + 2)), sq_nonneg ((x) * (x + 1) * (x + 2)), sq_nonneg (x - 5), sq_nonneg (x + 6), sq_nonneg (x + 5)]
  interval_cases x <;> omega