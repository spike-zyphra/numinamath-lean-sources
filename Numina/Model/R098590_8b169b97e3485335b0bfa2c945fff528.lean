import Mathlib

theorem algebra_183126 {z : ℂ} (hz : z + 9 = 10 * (z.1 - Complex.I * z.2) + 22 * Complex.I) :
    Complex.abs z = Real.sqrt 5 := by
  have eq1 := congr_arg Complex.re hz
  have eq2 := congr_arg Complex.im hz
  simp [Complex.add_re, Complex.ofReal_re, Complex.I_re, Complex.add_im, Complex.ofReal_im, Complex.I_im, Complex.mul_re, Complex.mul_im] at eq1 eq2
  have ha : z.re = 1 := by linarith
  have hb : z.im = 2 := by linarith
  simp [Complex.abs, Complex.normSq, ha, hb]
  <;> ring_nf <;> norm_num