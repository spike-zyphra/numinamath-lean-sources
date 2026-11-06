import Mathlib

theorem algebra_19828 : Real.sqrt (2/3) = (Real.sqrt 6)/3 := by
  have h1 : Real.sqrt (2 / 3) = Real.sqrt 2 / Real.sqrt 3 := by 
    field_simp [Real.sqrt_div]
  have h2 : Real.sqrt 6 = Real.sqrt 2 * Real.sqrt 3 := by
    calc
      Real.sqrt 6 = Real.sqrt (2 * 3) := by norm_num
      _ = Real.sqrt 2 * Real.sqrt 3 := by rw [Real.sqrt_mul (by norm_num)]
  rw [h1]
  rw [h2]
  have h3 : Real.sqrt 3 > 0 := by positivity
  field_simp [h3]
  <;> ring_nf <;> norm_num
  <;> ring