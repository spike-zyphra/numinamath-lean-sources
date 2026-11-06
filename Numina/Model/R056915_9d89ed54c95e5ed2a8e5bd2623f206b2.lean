import Mathlib

theorem algebra_1379 : Real.sqrt (2005 * 2006 * 2007 * 2008 + 1) - 2006^2 = 2005 := by
  have h1 : Real.sqrt (2005 * 2006 * 2007 * 2008 + 1) = (2006^2 + 2006 - 1 : ℝ) := by 
    have h2 : (2006^2 + 2006 - 1 : ℝ) ^ 2 = (2005 * 2006 * 2007 * 2008 + 1 : ℝ) := by
      norm_num
    have h3 : (2006^2 + 2006 - 1 : ℝ) ≥ 0 := by
      norm_num
    rw [← h2]
    field_simp [Real.sqrt_sq h3]
  rw [h1]
  norm_num