import Mathlib

theorem algebra_196095 {x y : ℝ} (hx : x = 0.8) (hy : y = 0.9) (h : (x * y + y * (1 - x)) / 1 = 0.88) :
    (y * (1 - x) + x * y) / 1 = 0.93 := by 
  rw [hx, hy] at h
  norm_num at h ⊢
  all_goals 
    linarith