import Mathlib

theorem algebra_100596 (z : ℂ) (hz : z * (z.1 - Complex.I * z.2) + (1 - 2 * Complex.I) * z + (1 + 2 * Complex.I) * (z.1 - Complex.I * z.2) = 3) :
    z.re + z.im ≥ -7 := by
  have eq1 := congr_arg Complex.re hz
  have eq2 := congr_arg Complex.im hz
  simp [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_add, pow_two] at eq1 eq2
  have h : (z.re + 1)^2 + (z.im + 2)^2 = 8 := by
    nlinarith
  nlinarith [sq_nonneg (z.re - z.im), sq_nonneg (z.re + z.im + 7), sq_nonneg (z.re - (-1 - 2)), sq_nonneg (z.im - (-2 - 2)), sq_nonneg (z.re + 1 - (z.im + 2)), sq_nonneg (z.re + 1 + (z.im + 2)), Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]