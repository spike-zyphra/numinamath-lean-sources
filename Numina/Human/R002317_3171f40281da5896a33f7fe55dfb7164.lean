import Mathlib

theorem algebra_84147 : abs (3 - Real.pi) = Real.pi - 3 := by
  have h : 3 - Real.pi < 0 := by linarith [Real.pi_gt_three]
  rw [abs_of_neg h]
  ring