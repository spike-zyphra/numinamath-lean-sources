import Mathlib

theorem algebra_299086 {z : ℂ} (hz : z = (Real.sqrt 3 / 2) + (1 / 2) * .I) : z ^ 2016 = 1 := by
  have hz1 : z = (Real.sqrt 3 / 2) + (1 / 2) * Complex.I := by
    exact hz
  have h1 : z ^ 3 = Complex.I := by
    rw [hz1]
    simp [pow_three, Complex.ext_iff, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
    field_simp
    <;> ring_nf <;> norm_num [Real.sqrt_sq]
  have h2 : z ^ 12 = 1 := by
    calc
      z ^ 12 = (z ^ 3) ^ 4 := by ring_nf
      _ = Complex.I ^ 4 := by rw [h1]
      _ = 1 := by norm_num [pow_succ, Complex.I_mul_I]
  calc
    z ^ 2016 = z ^ (12 * 168) := by norm_num
    _ = (z ^ 12) ^ 168 := by rw [pow_mul]
    _ = 1 ^ 168 := by rw [h2]
    _ = 1 := by norm_num