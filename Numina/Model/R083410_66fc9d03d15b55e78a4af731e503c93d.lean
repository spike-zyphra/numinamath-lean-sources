import Mathlib

theorem number_theory_277804 :
    (|(1 : ℝ) / 9 - 0| < |(1 : ℝ) / 2 - 0| ∧
     |(1 : ℝ) / 9 - 0| < |(1 : ℝ) / 8 - 0| ∧
     |(1 : ℝ) / 9 - 0| < |(1 : ℝ) / 3 - 0| ∧
     |(1 : ℝ) / 9 - 0| < |(1 : ℝ) / 6 - 0|) := by 
  have h1 : |(1 : ℝ) / 9 - 0| = (1 : ℝ) / 9 := by
    norm_num [abs_of_nonneg]
  have h2 : |(1 : ℝ) / 2 - 0| = (1 : ℝ) / 2 := by
    norm_num [abs_of_nonneg]
  have h3 : |(1 : ℝ) / 8 - 0| = (1 : ℝ) / 8 := by
    norm_num [abs_of_nonneg]
  have h4 : |(1 : ℝ) / 3 - 0| = (1 : ℝ) / 3 := by
    norm_num [abs_of_nonneg]
  have h5 : |(1 : ℝ) / 6 - 0| = (1 : ℝ) / 6 := by
    norm_num [abs_of_nonneg]
  rw [h1, h2, h3, h4, h5]
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · norm_num
  · norm_num