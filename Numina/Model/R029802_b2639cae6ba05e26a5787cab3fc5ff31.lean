import Mathlib

theorem number_theory_6109 (x y : ℤ) : x ^ 2 + 2 * y ^ 2 ≠ 203 := by 
  by_contra h 
  have h1 : x ^ 2 + 2 * y ^ 2 = 203 := by 
    omega 
  have h2 : x ≤ 14 := by
    nlinarith [sq_nonneg (x : ℤ), sq_nonneg (y : ℤ)]
  have h3 : x ≥ -14 := by
    nlinarith [sq_nonneg (x : ℤ), sq_nonneg (y : ℤ)]
  have h4 : y ≤ 10 := by
    nlinarith [sq_nonneg (x : ℤ), sq_nonneg (y : ℤ)]
  have h5 : y ≥ -10 := by
    nlinarith [sq_nonneg (x : ℤ), sq_nonneg (y : ℤ)]
  interval_cases x <;> interval_cases y <;> omega