import Mathlib

theorem algebra_132443 {z : ℂ} (hz : z + Complex.abs z = 2 + 8 * Complex.I) :
    (Complex.abs z)^2 = 289 := by
  have eq1 := congr_arg Complex.re hz
  have eq2 := congr_arg Complex.im hz
  simp [Complex.add_re, Complex.ofReal_re, Complex.I_re, Complex.add_im, Complex.ofReal_im, Complex.I_im] at eq1 eq2
  have h1 : z.im = 8 := by linarith
  have eq3 : Complex.abs z = Real.sqrt (z.re^2 + z.im^2) := by
    simp [Complex.abs, Complex.normSq]
    <;> ring
  rw [eq3] at eq1
  have h3 : z.re = -15 := by
    have eq4 : Real.sqrt (z.re^2 + (z.im) ^ 2) = Real.sqrt (z.re^2 + (8 : ℝ) ^ 2) := by
      rw [h1]
      all_goals
        ring
    rw [eq4] at eq1
    have h4 : Real.sqrt (z.re^2 + (8 : ℝ) ^ 2) ≥ 0 := Real.sqrt_nonneg (z.re^2 + (8 : ℝ) ^ 2)
    have h5 : Real.sqrt (z.re^2 + (8 : ℝ) ^ 2) = 2 - z.re := by linarith
    have h6 : (Real.sqrt (z.re^2 + (8 : ℝ) ^ 2)) ^ 2 = (2 - z.re) ^ 2 := by
      rw [h5]
    have h7 : (Real.sqrt (z.re^2 + (8 : ℝ) ^ 2)) ^ 2 = z.re^2 + (8 : ℝ) ^ 2 := Real.sq_sqrt (by positivity)
    rw [h7] at h6
    nlinarith
  have eq4 : Complex.abs z = 17 := by
    rw [eq3]
    rw [h3, h1]
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
  rw [eq4]
  all_goals
    norm_num