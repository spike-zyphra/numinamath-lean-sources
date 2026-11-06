import Mathlib

/- How many one-thirds are in one-sixth? -/
theorem algebra_16061 : (1 / 6 : ℝ) / (1 / 3) = 1 / 2 := by 
  field_simp
  norm_num