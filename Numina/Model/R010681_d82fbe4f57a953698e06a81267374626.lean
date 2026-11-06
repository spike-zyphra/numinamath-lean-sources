import Mathlib

theorem algebra_17151 : (Real.sqrt 338 / Real.sqrt 288) + (Real.sqrt 150 / Real.sqrt 96) = 7 / 3 := by 
  have h1 : Real.sqrt 338 / Real.sqrt 288 = 13 / 12 := by 
    have h2 : Real.sqrt 338 / Real.sqrt 288 = Real.sqrt (338 / 288) := by 
      field_simp [Real.sqrt_div]
    rw [h2]
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf <;> norm_num
  have h3 : Real.sqrt 150 / Real.sqrt 96 = 5 / 4 := by 
    have h4 : Real.sqrt 150 / Real.sqrt 96 = Real.sqrt (150 / 96) := by 
      field_simp [Real.sqrt_div]
    rw [h4]
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf <;> norm_num
  rw [h1, h3]
  norm_num