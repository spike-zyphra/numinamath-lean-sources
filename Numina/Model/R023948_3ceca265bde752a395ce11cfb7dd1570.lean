import Mathlib

theorem algebra_187649 {y x n : ℤ} (h1 : 2014 + y = 2015 + x) (h2 : 2015 + x = 2016 + n)
    (h3 : y * x * n = 504) : y * x + x * n = 128 := by 
  have eq1 : y = 1 + x := by
    linarith
  have eq2 : x = 1 + n := by 
    linarith
  have eq3 : y = 2 + n := by 
    rw [eq1]
    rw [eq2]
    all_goals linarith
  rw [eq3, eq2] at h3 
  have h4 : n = 7 := by 
    have h5 : n ≤ 8 := by 
      nlinarith [sq_nonneg (n - 7 : ℤ), sq_nonneg ((n + 1) : ℤ), sq_nonneg ((n) : ℤ), sq_nonneg ((n + 8) : ℤ)]
    have h6 : n ≥ -9 := by 
      nlinarith [sq_nonneg (n - 7 : ℤ), sq_nonneg ((n + 1) : ℤ), sq_nonneg ((n) : ℤ), sq_nonneg ((n + 8) : ℤ)]
    interval_cases n <;> omega
  have hx : x = 8 := by 
    rw [eq2]
    linarith 
  have hy : y = 9 := by 
    rw [eq3]
    linarith
  rw [hy, hx]
  nlinarith