import Mathlib

theorem number_theory_129350 : 10001 ^ 2 = 100020001 ∧ 100010001 ^ 2 = 10002000300020001 ∧ √1000200030004000300020001 = 1000100010001 := by
  constructor
  · -- Show that 10001^2 = 100020001
    norm_num
  constructor
  · -- Show that 100010001^2 = 10002000300020001
    norm_num
  · -- Show that sqrt(1000200030004000300020001) = 1000100010001
    have h1 : (1000100010001 : ℝ) ^ 2 = (1000200030004000300020001 : ℝ) := by
      norm_num
    have h2 : Real.sqrt (1000200030004000300020001 : ℝ) = (1000100010001 : ℝ) := by
      rw [← h1]
      rw [Real.sqrt_sq]
      all_goals norm_num
    rw [h2]
    all_goals norm_num