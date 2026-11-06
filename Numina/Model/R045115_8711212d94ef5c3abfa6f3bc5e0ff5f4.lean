import Mathlib

theorem algebra_147259 (x : ℝ) (hx : x > 0) (h : 3 = x * 0.07 * 0.61) :
    x > 70 := by
  have h1 : x = 3 / (0.07 * 0.61 : ℝ) := by
    field_simp
    linarith
  rw [h1]
  norm_num
  all_goals linarith