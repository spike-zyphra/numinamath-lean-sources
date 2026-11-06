import Mathlib

theorem inequalities_2403 (a : ℝ) (ha : a < -1) : a < -1 ∧ -1 < 1 ∧ 1 < -a := by 
  constructor
  · linarith
  constructor
  · norm_num
  · linarith