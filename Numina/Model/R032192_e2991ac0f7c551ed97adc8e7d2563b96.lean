import Mathlib

theorem algebra_12772 {n : ℕ} (hn : n > 3) (h : n = 5) :
    (3 : ℚ) / n = 3 / 5 := by 
  rw [h]
  all_goals norm_num