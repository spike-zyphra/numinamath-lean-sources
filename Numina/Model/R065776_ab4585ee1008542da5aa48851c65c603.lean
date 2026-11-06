import Mathlib

theorem algebra_282781 (total_money : ℝ) (h : total_money = 100) :
    (total_money * (1 / 4)) + (total_money * (1 / 10)) = 35 := by 
  rw [h]
  norm_num