import Mathlib

theorem algebra_2223 {x : ℝ} (hx : x * 0.8 = 1.2) : x * 1 = 1.5 := by
  have hx1 : x = 1.5 := by
    norm_num at hx ⊢
    linarith
  rw [hx1]
  all_goals norm_num