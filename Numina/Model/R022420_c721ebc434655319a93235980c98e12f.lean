import Mathlib

theorem algebra_12310 {z : ℂ} (hz : z = (Real.sqrt 3 / 2) + (1 / 2) * .I) :
    z ^ 2016 = 1 := by
  have h1 : z = (Real.sqrt 3 / 2) + (1 / 2) * Complex.I := by simp [hz]
  have h2 : z ^ 3 = Complex.I := by
    rw [h1]
    simp [pow_three, Complex.ext_iff, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
    field_simp
    <;> ring_nf <;> norm_num [Real.sqrt_sq]
  have h3 : z ^ 12 = 1 := by
    calc
      z ^ 12 = (z ^ 3) ^ 4 := by ring
      _ = Complex.I ^ 4 := by rw [h2]
      _ = 1 := by
        simp [pow_succ, Complex.I_mul_I]
  calc
    z ^ 2016 = (z ^ 12) ^ 168 := by ring
    _ = 1 ^ 168 := by rw [h3]
    _ = 1 := by norm_num