import Mathlib

theorem algebra_8116 {x y : ℝ} (h : x^2 + 2 * x + y^2 + 4 * y + 5 = 0) : (x + y)^2 = 9 := by
  have h1 : (x + 1)^2 + (y + 2)^2 = 0 := by
    ring_nf at h ⊢
    linarith
  have h2 : (x + 1)^2 = 0 := by
    linarith [sq_nonneg (x + 1), sq_nonneg (y + 2)]
  have h3 : x + 1 = 0 := by
    rw [sq_eq_zero_iff] at h2
    exact h2
  have hx : x = -1 := by
    linarith
  have h4 : (y + 2)^2 = 0 := by
    linarith [sq_nonneg (x + 1), sq_nonneg (y + 2)]
  have h5 : y + 2 = 0 := by
    rw [sq_eq_zero_iff] at h4
    exact h4
  have hy : y = -2 := by
    linarith
  rw [hx, hy]
  norm_num