import Mathlib

theorem algebra_8223
  {m n p : ℝ}
  (hmn : m^2 - 2 * p = 7)
  (hnp : n^2 - 6 * m = -17)
  (hpp : p^2 + 2 * n = -1) :
  m + n + p = 3 := by

  have eq1 : (m - 3) ^ 2 + (n + 1) ^ 2 + (p - 1) ^ 2 = 0 := by
    nlinarith

  have hm1 : (m - 3) ^ 2 = 0 := by
    nlinarith [sq_nonneg (m - 3), sq_nonneg (n + 1), sq_nonneg (p - 1)]

  have hm2 : m - 3 = 0 := by
    rwa [sq_eq_zero_iff] at hm1

  have hm3 : m = 3 := by linarith

  have hn1 : (n + 1) ^ 2 = 0 := by
    nlinarith [sq_nonneg (m - 3), sq_nonneg (n + 1), sq_nonneg (p - 1)]

  have hn2 : n + 1 = 0 := by
    rwa [sq_eq_zero_iff] at hn1

  have hn3 : n = -1 := by linarith

  have hp1 : (p - 1) ^ 2 = 0 := by
    nlinarith [sq_nonneg (m - 3), sq_nonneg (n + 1), sq_nonneg (p - 1)]

  have hp2 : p - 1 = 0 := by
    rwa [sq_eq_zero_iff] at hp1

  have hp3 : p = 1 := by linarith

  linarith