import Mathlib

theorem algebra_275544 {P Q : ℝ} (hP : P ≠ 0) (hQ : Q ≠ 0)
    (h : 50 / 100 * P = 20 / 100 * Q) : P / Q * 100 = 40 := by
  have h1 : P = (2 / 5) * Q := by 
    linarith
  have h2 : P / Q = 2 / 5 := by
    have h3 : P = (2 / 5) * Q := h1
    field_simp [hQ]
    linarith
  rw [h2]
  all_goals norm_num
  all_goals linarith