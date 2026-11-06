import Mathlib

theorem algebra_285264 (total_money : ℝ) (num_charities : ℕ) (h : total_money = 3109) (h2 : num_charities = 25) :
    total_money / num_charities = 124.36 := by
  rw [h, h2]
  norm_num