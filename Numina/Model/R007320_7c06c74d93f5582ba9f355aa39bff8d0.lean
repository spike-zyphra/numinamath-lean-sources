import Mathlib

theorem algebra_10615 : (Real.sqrt 2 / Real.sqrt 3) * (Real.sqrt 4 / Real.sqrt 5) * (Real.sqrt 6 / Real.sqrt 7) =
    4 * Real.sqrt 35 / 35 := by
  have h1 : Real.sqrt 2 / Real.sqrt 3 = Real.sqrt (2 / 3) := by
    field_simp [Real.sqrt_div]
  have h2 : Real.sqrt 4 / Real.sqrt 5 = Real.sqrt (4 / 5) := by
    field_simp [Real.sqrt_div]
  have h3 : Real.sqrt 6 / Real.sqrt 7 = Real.sqrt (6 / 7) := by
    field_simp [Real.sqrt_div]
  rw [h1, h2, h3]
  have h4 : Real.sqrt (2 / 3 : ℝ) * Real.sqrt (4 / 5 : ℝ) * Real.sqrt (6 / 7 : ℝ) =
          Real.sqrt ((2 / 3 : ℝ) * (4 / 5 : ℝ) * (6 / 7 : ℝ)) := by
    rw [← Real.sqrt_mul (by norm_num)]
    rw [← Real.sqrt_mul (by norm_num)]
    all_goals norm_num
  rw [h4]
  have h5 : (2 / 3 : ℝ) * (4 / 5 : ℝ) * (6 / 7 : ℝ) = (16 / 35 : ℝ) := by norm_num
  rw [h5]
  have h6 : Real.sqrt (16 / 35 : ℝ) = Real.sqrt 16 / Real.sqrt 35 := by 
    field_simp [Real.sqrt_div]
  have h7 : Real.sqrt (16 : ℝ) = 4 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
  rw [h6, h7]
  have h8 : Real.sqrt 35 ^ 2 = 35 := Real.sq_sqrt (by norm_num)
  field_simp [h8]
  <;> ring_nf <;> norm_num [Real.sq_sqrt]
  <;> ring