import Mathlib

theorem algebra_209708 : Real.sqrt (1 + 2011^2 + (2011 / 2012)^2) + 2011 / 2012 = 2012 := by
  have h1 : Real.sqrt (1 + 2011^2 + (2011 / 2012)^2) = (2012 - (2011 / 2012)) := by
    have h2 : (2012 - (2011 / 2012) : ℝ) ^ 2 = (1 + 2011 ^ 2 + (2011 / 2012) ^ 2 : ℝ) := by norm_num
    have h3 : (2012 - (2011 / 2012) : ℝ) ≥ 0 := by norm_num
    rw [←h2]
    field_simp [Real.sqrt_sq h3]
  rw [h1]
  norm_num