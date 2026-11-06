import Mathlib

theorem algebra_21891 {z : ℂ} (hz : 2 - 3 * Complex.I * z = 3 + 2 * Complex.I * z) :
    z = Complex.I / 5 := by
  have eq1 := congr_arg Complex.re hz
  have eq2 := congr_arg Complex.im hz
  simp [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im] at eq1 eq2
  have hx : z.re = 0 := by
    nlinarith
  have hy : z.im = 1 / 5 := by
    nlinarith
  simp [Complex.ext_iff, hx, hy]
  all_goals norm_num