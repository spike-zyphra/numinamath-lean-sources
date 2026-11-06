import Mathlib

theorem algebra_205260 {x y : ℝ} (h1 : 2 * x = 23) (h2 : 2 * y = 22)
    (h3 : x = y) (h4 : 8 * x = 3 * y) :
    x = 5 ∧ y = 3 := by 
  have hx1 : x = 23 / 2 := by
    linarith
  have hy1 : y = 11 := by
    linarith
  have h5 : x = y := h3
  rw [hx1, hy1] at h5 
  all_goals norm_num at h5 
  all_goals 
    linarith