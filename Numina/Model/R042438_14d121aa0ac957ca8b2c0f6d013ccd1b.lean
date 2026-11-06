import Mathlib

theorem algebra_297344 {x y : ℝ} (h1 : x^2 - y^2 + x - 2 * y - 6 = 0) (h2 : 2 * x * y + 2 * x + y - 4 = 0) :
    (x, y) = (2, 0) ∨ (x, y) = (-3, -2) := by
  have h3 : (x - 2) * (x + 3) = 0 := by
    nlinarith [sq_nonneg (x + 3), sq_nonneg (y - 0), sq_nonneg (x - 2), sq_nonneg (y + 2), sq_nonneg (x - y)]
  cases' (mul_eq_zero.mp h3) with h4 h5
  · -- When x = 2
    have hx1 : x = 2 := by linarith
    have hy1 : y = 0 := by
      rw [hx1] at h2
      linarith
    left
    simp [hx1, hy1]
  · -- When x = -3
    have hx2 : x = -3 := by linarith
    have hy2 : y = -2 := by
      rw [hx2] at h2
      nlinarith
    right
    simp [hx2, hy2]