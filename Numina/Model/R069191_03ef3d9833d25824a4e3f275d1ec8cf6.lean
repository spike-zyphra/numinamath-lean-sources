import Mathlib

theorem algebra_319567 {a : ℝ} (ha : a = Real.sqrt 3 - 1) : a^2012 + 2 * a^2011 - 2 * a^2010 = 0 := by
  have h1 : a + 1 = Real.sqrt 3 := by 
    rw [ha]
    all_goals ring
  have h2 : (a + 1)^2 = 3 := by
    rw [h1]
    rw [Real.sq_sqrt]
    all_goals norm_num
  have h3 : a^2 + 2 * a - 2 = 0 := by
    nlinarith
  have h4 : a^2012 + 2 * a^2011 - 2 * a^2010 = a^2010 * (a^2 + 2 * a - 2) := by
    ring
  rw [h4, h3]
  norm_num