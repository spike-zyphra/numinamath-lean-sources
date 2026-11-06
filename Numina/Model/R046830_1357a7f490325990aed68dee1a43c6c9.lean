import Mathlib

theorem algebra_306661 {x y : ℝ} (h : x^2 + 3 * y^2 - 12 * y + 12 = 0) : y^x = 1 := by
  have h1 : x^2 + 3 * (y - 2)^2 = 0 := by
    nlinarith [sq_nonneg (y - 2), sq_nonneg x]
  have hx1 : x^2 = 0 := by
    linarith [sq_nonneg (y - 2), sq_nonneg x]
  have hy1 : (y - 2)^2 = 0 := by
    nlinarith [sq_nonneg (y - 2), sq_nonneg x]
  have hx2 : x = 0 := by
    rw [sq_eq_zero_iff] at hx1
    linarith
  have hy2 : y = 2 := by
    rw [sq_eq_zero_iff] at hy1
    linarith
  rw [hx2, hy2]
  all_goals norm_num