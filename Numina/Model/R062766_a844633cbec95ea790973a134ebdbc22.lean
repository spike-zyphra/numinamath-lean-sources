import Mathlib

theorem number_theory_257596 : |(2^3000 : ℝ) - 3^2006| > 1 / 2 := by
  have h3 : |((2 : ℝ) ^ 3000) - (3 : ℝ) ^ 2006| = (3 : ℝ) ^ 2006 - (2 : ℝ) ^ 3000 := by
    have h4 : ((2 : ℝ) ^ 3000) - (3 : ℝ) ^ 2006 < 0 := by
      norm_num
    rw [abs_of_neg h4]
    all_goals nlinarith
  rw [h3]
  norm_num