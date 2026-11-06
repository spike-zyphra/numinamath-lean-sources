import Mathlib

theorem algebra_269004 {z : ℂ} (hz : z = Real.sqrt 3 / 2 + 1 / 2 * .I) :
    z ^ 2016 = 1 := by
  have h1 : z = Real.sqrt 3 / 2 + 1 / 2 * Complex.I := by
    exact hz
  -- Calculate z^3 = i
  have h2 : z ^ 3 = Complex.I := by 
    rw [h1]
    simp [pow_three, Complex.ext_iff, Complex.I_mul_I, mul_add, add_mul, pow_two, Complex.I_sq]
    field_simp
    <;> ring_nf <;> norm_num
  -- Calculate z^12 = 1
  have h3 : z ^ 12 = 1 := by 
    calc 
      z ^ 12 = (z ^ 3) ^ 4 := by ring
      _ = Complex.I ^ 4 := by rw [h2]
      _ = 1 := by 
        simp [pow_succ]
  -- Calculate z^2016 = (z^12)^168 = 1
  calc 
    z ^ 2016 = (z ^ 12) ^ 168 := by 
      calc 
        z ^ 2016 = z ^ (12 * 168) := by norm_num
        _ = (z ^ 12) ^ 168 := by rw [pow_mul]
    _ = (1) ^ 168 := by 
      rw [h3]
    _ = 1 := by 
      norm_num