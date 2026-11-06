import Mathlib

theorem algebra_208569 (n : ℤ) : ¬(n-20)^3 + 2*n^3 = (n+20)^3 := by 
  intro h
  have eq2 : n ^ 3 - 60 * n ^ 2 - 8000 = 0 := by
    nlinarith [sq_nonneg (n ^ 2), sq_nonneg ((n : ℤ) - 20), sq_nonneg ((n : ℤ) + 20), h]
  have h3 : n ≤ 80 := by
    nlinarith [sq_nonneg (n ^ 2 -  60 * n), sq_nonneg (n - 80), sq_nonneg (n + 10), sq_nonneg (n ^ 2 - 1200), sq_nonneg ((n - 80) * (n)), sq_nonneg ((n ^ 2) * (n)), sq_nonneg ((n - 80) * (n - 80))]
  have h4 : n ≥ -20 := by
    nlinarith [sq_nonneg (n ^ 2 -  60 * n), sq_nonneg (n + 10), sq_nonneg (n - 80), sq_nonneg (n + 20), sq_nonneg (n ^ 2 - 1200), sq_nonneg ((n + 20) * (n)), sq_nonneg ((n ^ 2) * (n)), sq_nonneg ((n + 20) * (n + 20))]
  interval_cases n <;> omega