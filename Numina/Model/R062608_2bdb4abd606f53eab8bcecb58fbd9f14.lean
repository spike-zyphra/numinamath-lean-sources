import Mathlib

open Real

theorem algebra_2657 : (1 / (sqrt 30 - sqrt 31)) = -(sqrt 30 + sqrt 31) := by
  have h1 : sqrt 30 - sqrt 31 ≠ 0 := by
    intro h
    have h2 : sqrt 30 = sqrt 31 := by linarith
    have h3 : (sqrt 30) ^ 2 = (sqrt 31) ^ 2 := by 
      rw [h2]
    rw [Real.sq_sqrt, Real.sq_sqrt] at h3
    all_goals norm_num at h3 ⊢ 
  field_simp [h1]
  <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (30 : ℝ) by norm_num : (30 : ℝ) > 0), 
      Real.sqrt_pos.mpr (show (0 : ℝ) < (31 : ℝ) by norm_num : (31 : ℝ) > 0), 
      Real.sq_sqrt (show (0 : ℝ) ≤ (30 : ℝ) by norm_num : (30 : ℝ) ≥ 0), 
      Real.sq_sqrt (show (0 : ℝ) ≤ (31 : ℝ) by norm_num : (31 : ℝ) ≥ 0)]