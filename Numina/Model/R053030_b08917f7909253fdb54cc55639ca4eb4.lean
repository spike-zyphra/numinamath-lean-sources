import Mathlib

theorem algebra_201579 {P : ℝ}
    (hP : P = 2 * (2007 * 2009 * 2011 * 2013 + 10 * 2010 * 2010 - 9) ^ ((1 : ℝ) / 4) - 4000) : P = 20 := by
  have h1 : ((2007 * 2009 * 2011 * 2013 + 10 * 2010 * 2010 - 9) : ℝ) = (2010 : ℝ) ^ 4 := by
    norm_num
  have h2 : ((2007 * 2009 * 2011 * 2013 + 10 * 2010 * 2010 - 9) : ℝ) ^ ((1 : ℝ) / 4) = (2010 : ℝ) := by
    rw [h1]
    have h5 : ((2010 : ℝ) ^ 4) ^ ((1 : ℝ) / 4) = (2010 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul]
      norm_num
      all_goals linarith
    exact h5
  rw [hP]
  rw [h2]
  norm_num