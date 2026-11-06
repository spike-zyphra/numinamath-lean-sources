import Mathlib

theorem algebra_289293 : (Real.logb 2 4) * (Real.logb 4 6) * (Real.logb 6 8) = 3 := by
  have h1 : Real.logb 2 4 = 2 := by
    rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
  have h2 : Real.logb 4 6 = Real.log 6 / Real.log 4 := by 
    field_simp [Real.logb]
  have h3 : Real.log 4 = 2 * Real.log 2 := by
    calc 
      Real.log 4 = Real.log (2 ^ 2) := by norm_num
      _ = 2 * Real.log 2 := by simp [Real.log_pow]
  have h4 : Real.logb 6 8 = Real.log 8 / Real.log 6 := by
    field_simp [Real.logb]
  have h5 : Real.log 8 = 3 * Real.log 2 := by
    calc 
      Real.log 8 = Real.log (2 ^ 3) := by norm_num
      _ = 3 * Real.log 2 := by simp [Real.log_pow]
  rw [h1, h2, h3, h4, h5]
  field_simp
  <;> ring_nf
  <;> field_simp
  <;> ring_nf
  <;> norm_num