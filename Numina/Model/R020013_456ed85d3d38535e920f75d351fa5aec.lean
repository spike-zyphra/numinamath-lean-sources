import Mathlib

theorem algebra_324197 {x : ℂ} (hx : x = (1 + Real.sqrt 5 * Complex.I) / 2) :
    2 * x ^ 3 + (x + 1) ^ 2 = Real.sqrt 5 * Complex.I - 5 / 2 := by
  rw [hx]
  simp [pow_two, pow_three, Complex.ext_iff, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  field_simp
  <;> ring_nf
  <;> norm_num [Real.sqrt_sq]