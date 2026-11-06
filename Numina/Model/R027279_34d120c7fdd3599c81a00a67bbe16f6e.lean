import Mathlib

theorem algebra_319851 {z : ℂ} (hz : Complex.abs z * (3 * z + 2 * .I) = 2 * (.I * z - 6)) :
    Complex.abs z = 2 := by
  have eq1 := congr_arg Complex.re hz
  have eq2 := congr_arg Complex.im hz
  have eq3 : (Complex.abs z) * (3 * z.re) = -12 - 2 * z.im := by
    simp [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, 
          Complex.I_re, Complex.I_im, Complex.abs] at eq1 ⊢
    linarith [eq1]
  have eq4 : (Complex.abs z) * (2 + 3 * z.im) = 2 * z.re := by
    simp [Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, 
          Complex.I_re, Complex.I_im, Complex.abs] at eq2 ⊢
    ring_nf at eq2 ⊢
    linarith [eq2]
  have eq5 : (Complex.abs z) * (3 * z.re) = -12 - 2 * z.im := by linarith [eq3]
  have eq6 : (Complex.abs z) * (2 + 3 * z.im) = 2 * z.re := by linarith [eq4]
  have h2 : Complex.abs z ≥ 0 := by positivity
  have h6 : Complex.abs z ^ 2 = z.re ^ 2 + z.im ^ 2 := by 
    have h1 : Complex.abs z = Real.sqrt (z.re ^ 2 + z.im ^ 2) := by
      simp [Complex.abs, Complex.normSq]
      <;> ring_nf
    rw [h1]
    rw [Real.sq_sqrt]
    positivity
  have h5 : Complex.abs z ^ 2 = z.re ^ 2 + z.im ^ 2 := h6
  have eq7 : (Complex.abs z) ^ 2 * (3 * z.re) ^ 2 = (-12 - 2 * z.im) ^ 2 := by
    have h7 : (Complex.abs z) * (3 * z.re) = -12 - 2 * z.im := by linarith [eq5]
    have h8 : ((Complex.abs z) * (3 * z.re)) ^ 2 = (-12 - 2 * z.im) ^ 2 := by 
      rw [h7]
    calc 
      (Complex.abs z) ^ 2 * (3 * z.re) ^ 2 
          = ((Complex.abs z) * (3 * z.re)) ^ 2 := by ring
      _ = (-12 - 2 * z.im) ^ 2 := by linarith [h8]
  have eq8 : (Complex.abs z) ^ 2 * (2 + 3 * z.im) ^ 2 = (2 * z.re) ^ 2 := by
    have h7 : (Complex.abs z) * (2 + 3 * z.im) = 2 * z.re := by linarith [eq6]
    have h8 : ((Complex.abs z) * (2 + 3 * z.im)) ^ 2 = (2 * z.re) ^ 2 := by 
      rw [h7]
    calc 
      (Complex.abs z) ^ 2 * (2 + 3 * z.im) ^ 2 
          = ((Complex.abs z) * (2 + 3 * z.im)) ^ 2 := by ring
      _ = (2 * z.re) ^ 2 := by linarith [h8]
  have h8 : Complex.abs z ^ 2 = 4 := by
    nlinarith [h5, sq_nonneg (z.re), sq_nonneg (z.im), sq_nonneg (z.re * z.im), sq_nonneg (z.re - z.im), sq_nonneg (z.re + z.im), sq_nonneg (z.re - (-8 / 5) : ℝ), sq_nonneg (z.im - (-6 / 5) : ℝ)]
  have h3 : Complex.abs z = 2 := by
    have h4 : Complex.abs z ^ 2 = 4 := h8
    have hk : Complex.abs z ≥ 0 := by positivity
    have hk2 : Complex.abs z = 2 := by
      nlinarith
    exact_mod_cast hk2
  exact_mod_cast h3