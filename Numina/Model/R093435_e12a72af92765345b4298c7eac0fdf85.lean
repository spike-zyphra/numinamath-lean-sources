import Mathlib

theorem algebra_133632 {x y : ℝ} (h : (6 * x - 5 * y) ^ 4 + (4 * y - 3) ^ 6 = 0) :
    x + y = 11 / 8 := by 
  have h1 : (6 * x - 5 * y) ^ 4 ≥ 0 := by positivity
  have h2 : (4 * y - 3) ^ 6 ≥ 0 := by positivity

  have h3 : (6 * x - 5 * y) ^ 4 = 0 := by linarith
  have h4 : (4 * y - 3) ^ 6 = 0 := by linarith

  have h5 : (6 * x - 5 * y) = 0 := by
    rw [pow_eq_zero_iff (by norm_num)] at h3
    linarith

  have h6 : (4 * y - 3) = 0 := by
    rw [pow_eq_zero_iff (by norm_num)] at h4
    linarith

  have hy1 : y = 3 / 4 := by linarith [h6]

  have hx1 : x = 5 / 8 := by
    rw [hy1] at h5
    linarith

  linarith [hx1, hy1]