import Mathlib

theorem algebra_20803 : (Real.sqrt 160 / Real.sqrt 252) * (Real.sqrt 245 / Real.sqrt 108) = 5 * Real.sqrt 42 / 27 := by
  have h1 : Real.sqrt 160 / Real.sqrt 252 = Real.sqrt (160 / 252) := by
    field_simp [Real.sqrt_div]
  have h2 : Real.sqrt 245 / Real.sqrt 108 = Real.sqrt (245 / 108) := by
    field_simp [Real.sqrt_div]
  rw [h1, h2]
  have h3 : Real.sqrt (160 / 252) * Real.sqrt (245 / 108) = Real.sqrt ((160 / 252) * (245 / 108)) := by
    rw [← Real.sqrt_mul (by norm_num)]
  rw [h3]
  have h4 : (160 / 252 : ℝ) * (245 / 108 : ℝ) = (350 / 243 : ℝ) := by
    norm_num
  rw [h4]
  have h5 : Real.sqrt (350 / 243 : ℝ) = (5 * Real.sqrt 42 / 27 : ℝ) := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf <;> norm_num
  rw [h5]
  all_goals norm_num