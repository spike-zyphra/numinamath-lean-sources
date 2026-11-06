import Mathlib

theorem algebra_327850 {m n : ℝ} (h : m^2 + n^2 + m * n + m - n + 1 = 0) :
    1 / m + 1 / n = 0 := by
  have h1 : m ≠ 0 := by
    by_contra h1
    rw [h1] at h
    have : n^2 + 1 = 0 := by nlinarith
    nlinarith [sq_nonneg n]
  have h2 : n ≠ 0 := by
    by_contra h2
    rw [h2] at h
    have : m^2 + 1 = 0 := by nlinarith
    nlinarith [sq_nonneg m]
  have h3 : (n - 1) ^ 2 = 0 := by
    nlinarith [sq_nonneg (m + 1), sq_nonneg (n - 1)]
  have hn1 : n = 1 := by
    nlinarith
  have hm1 : m = -1 := by
    rw [hn1] at h
    nlinarith [sq_nonneg (m + 1)]
  rw [hm1, hn1]
  norm_num