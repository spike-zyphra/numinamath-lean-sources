import Mathlib

theorem algebra_17168 (n : ℝ) (h : n = 3.45) : round (n * 10) = 35 := by 
  rw [h]
  norm_num [round_eq, Int.floor_eq_iff]
  <;> norm_num
  <;> tauto
  all_goals norm_num
  <;> tauto