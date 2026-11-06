import Mathlib

theorem other_269148 :
   (|(1.01 : ℝ) - 1| < |(0.50 : ℝ) - 1| ∧
    |(1.01 : ℝ) - 1| < |(0.90 : ℝ) - 1| ∧
    |(1.01 : ℝ) - 1| < |(0.95 : ℝ) - 1| ∧
    |(1.01 : ℝ) - 1| < |(1.15 : ℝ) - 1|) := by
  have h1 : |(1.01 : ℝ) - 1| = 0.01 := by
    norm_num [abs]
  have h2 : |(0.50 : ℝ) - 1| = 0.5 := by
    norm_num [abs]
  have h3 : |(0.90 : ℝ) - 1| = 0.1 := by
    norm_num [abs]
  have h4 : |(0.95 : ℝ) - 1| = 0.05 := by
    norm_num [abs]
  have h5 : |(1.15 : ℝ) - 1| = 0.15 := by
    norm_num [abs]

  rw [h1, h2, h3, h4, h5]
  all_goals norm_num