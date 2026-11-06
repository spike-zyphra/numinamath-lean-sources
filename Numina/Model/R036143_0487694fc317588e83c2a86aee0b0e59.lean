import Mathlib

theorem algebra_21147 : Real.sqrt 32670 = 33 * Real.sqrt 30 := by
  have h1 : (33 * Real.sqrt 30) ^2 = (32670 : ℝ) := by
    calc
      (33 * Real.sqrt 30) ^2 = (33 : ℝ) ^2 * (Real.sqrt 30) ^2 := by ring
      _ = (33 : ℝ) ^2 * (30 : ℝ) := by rw [Real.sq_sqrt]; positivity
      _ = (1089 : ℝ) * (30 : ℝ) := by norm_num
      _ = (32670 : ℝ) := by norm_num
  have h2 : 0 ≤ (33 * Real.sqrt 30 : ℝ) := by
    positivity
  rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num [h1, h2]