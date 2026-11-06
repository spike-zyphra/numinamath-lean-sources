import Mathlib

theorem algebra_20808 {x : ℤ} (hx : x * (x + 1) * (x + 2) = 120) (h : 120 / ((x + x + 1 + x + 2) / 3) = 24) :
    x + 2 = 6 := by
  have h1 : x ≤ 6 := by
    nlinarith [sq_nonneg (x - 4 : ℤ), sq_nonneg (x * (x + 2) : ℤ), sq_nonneg ((x + 1) * (x + 2)) , sq_nonneg (x * (x + 1)), sq_nonneg (x * (x + 1) * (x + 2)), sq_nonneg (x - 4 : ℤ)]
  have h2 : x ≥ -6 := by
    nlinarith [sq_nonneg (x + 5 : ℤ), sq_nonneg (x * (x + 2) : ℤ), sq_nonneg ((x + 1) * (x + 2)), sq_nonneg (x * (x + 1) : ℤ), sq_nonneg (x * (x + 1) * (x + 2)), sq_nonneg (x + 5 : ℤ)]
  interval_cases x <;> norm_num at h hx <;> omega