import Mathlib

theorem algebra_14213 (r : ℝ) (h : (1 + 6 / 100 / 12) ^ 12 = (1 + r / 100) ^ 1) :
    round (r * 100) / 100 = (6.17 : ℝ) := by
  have eq1 : (1 + r / 100 : ℝ) = (1 + (6 / 100 : ℝ) / 12) ^ 12 := by
    nlinarith
  have eq2 : r = 100 * ((1 + (6 / 100 : ℝ) / 12) ^ 12 - 1) := by
    have eq3 : (1 + r / 100 : ℝ) = (1 + (6 / 100 : ℝ) / 12) ^ 12 := eq1
    have eq4 : r / 100 = ((1 + (6 / 100 : ℝ) / 12) ^ 12 - 1 : ℝ) := by
      linarith [eq3]
    have eq5 : r = 100 * ((1 + (6 / 100 : ℝ) / 12) ^ 12 - 1 : ℝ) := by
      linarith [eq4]
    linarith [eq5]
  have eq3 : round (r * 100) = 617 := by
    rw [eq2]
    norm_num [round_eq]
    <;> norm_num
  rw [eq3]
  all_goals norm_num