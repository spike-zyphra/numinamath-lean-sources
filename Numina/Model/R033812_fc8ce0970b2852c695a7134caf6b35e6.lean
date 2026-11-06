import Mathlib

theorem algebra_21504 {z : ℂ} (hz : z^2 = 156 + 65 * .I) : Complex.abs z = 13 := by
  have eq1 : z.re^2 - z.im^2 = 156 := by
    have h1 := congr_arg Complex.re hz
    simp [pow_two, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re,
      Complex.I_im] at h1
    linarith
  have eq2 : 2 * z.re * z.im = 65 := by
    have h2 := congr_arg Complex.im hz
    simp [pow_two, Complex.add_im, Complex.mul_im, Complex.ofReal_im, Complex.I_re,
      Complex.I_im] at h2
    linarith
  have eq3 : z.re^2 + z.im^2 = 169 := by
    nlinarith [sq_nonneg (z.re - z.im), sq_nonneg (z.re + z.im),
      sq_nonneg (2 * z.re * z.im - 13)]
  have eq4 : Complex.abs z = Real.sqrt (z.re^2 + z.im^2) := by
    simp [Complex.abs, Complex.normSq]
    <;> ring
  rw [eq4]
  rw [eq3]
  rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num