import Mathlib

theorem algebra_29424 {x y : ℝ} (h : y ^ 4 + 4 * y ^ 2 * x - 11 * y ^ 2 + 4 * x * y - 8 * y + 8 * x ^ 2 - 40 * x + 52 = 0) :
    (x, y) = (1, 2) ∨ (x, y) = (2.5, -1) := by

  have h1 : (y - 2) ^ 2 * (y + 1) ^ 2 = 0 := by
    nlinarith [sq_nonneg (x + (y ^ 2 + y - 10) / 4), sq_nonneg (y - 2), sq_nonneg (y + 1), sq_nonneg (x - (1:ℝ)), sq_nonneg (x - (5/2:ℝ)), sq_nonneg (y ^ 2 - 4 * y + 4), sq_nonneg (y ^ 2 + 2 * y + 1)]
  cases' (mul_eq_zero.1 h1) with h2 h3
  · -- When $(y - 2) ^ 2 = 0$, so $y = 2$.
    have hy2 : y = 2 := by
      nlinarith [pow_eq_zero h2]
    have hx1 : x = 1 := by
      rw [hy2] at h
      nlinarith
    left
    simp [hx1, hy2]
  · -- When $(y + 1) ^ 2 = 0$, so $y = -1$.
    have hy1 : y = -1 := by
      nlinarith [pow_eq_zero h3]
    have hx2 : x = (2.5 : ℝ) := by
      rw [hy1] at h
      ring_nf at h
      nlinarith
    right
    simp [hx2, hy1]