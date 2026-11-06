import Mathlib

theorem algebra_115470 : ⌊(Real.sqrt (2009 * 2011 * 2013 * 2015 + 16) / 2015)⌋ = 2009 := by
  have h1 : Real.sqrt (2009 * 2011 * 2013 * 2015 + 16) = (2012 ^ 2 - 5 : ℝ) := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
  have h2 : Real.sqrt (2009 * 2011 * 2013 * 2015 + 16) / 2015 = (2009 + 4 / 2015 : ℝ) := by
    rw [h1]
    norm_num
  rw [h2]
  norm_num [Int.floor_eq_iff]