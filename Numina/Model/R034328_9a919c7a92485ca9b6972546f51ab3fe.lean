import Mathlib

theorem algebra_94106 : ((1 + 1 / 3 : ℝ) * (1 + 1 / 5 : ℝ) * (1 + 1 / 7 : ℝ)) / Real.sqrt ((1 - 1 / 3 ^ 2 : ℝ) * (1 - 1 / 5 ^ 2 : ℝ) * (1 - 1 / 7 ^ 2 : ℝ)) = 2 := by
  have h1 : ((1 + 1 / 3 : ℝ) * (1 + 1 / 5 : ℝ) * (1 + 1 / 7 : ℝ)) = (192 / 105 : ℝ) := by norm_num
  have h2 : ((1 - 1 / 3 ^ 2 : ℝ) * (1 - 1 / 5 ^ 2 : ℝ) * (1 - 1 / 7 ^ 2 : ℝ)) = (1024 / 1225 : ℝ) := by norm_num
  have h3 : Real.sqrt ((1024 / 1225 : ℝ)) = (32 / 35 : ℝ) := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
  rw [h1, h2, h3]
  norm_num