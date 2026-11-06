import Mathlib

theorem algebra_96233 {z : ℂ} (hz : z + Complex.abs z = 2 + 8 * .I) :
    Complex.abs z ^ 2 = 289 := by
  have eq1 := congr_arg Complex.re hz
  have eq2 := congr_arg Complex.im hz
  simp [Complex.add_re, Complex.ofReal_re, Complex.I_re, Complex.add_im, Complex.ofReal_im, 
        Complex.I_im] at eq1 eq2
  have h1 : z.im = 8 := by linarith
  have h2 : Complex.abs z = Real.sqrt (z.re ^ 2 + z.im ^ 2) := by
    simp [Complex.abs, Complex.normSq]
    <;> ring_nf
  rw [h2] at eq1
  have eq3 : z.re + Real.sqrt (z.re ^ 2 + (8) ^ 2) = 2 := by
    rw [show z.im = (8 : ℝ) by linarith [h1] ] at eq1
    linarith
  have h4 : z.re = -15 := by
    have h5 : Real.sqrt (z.re ^ 2 + (8) ^ 2) = 2 - z.re := by
      linarith [eq3]
    have h6 : Real.sqrt (z.re ^ 2 + (8) ^ 2) ≥ 0 := Real.sqrt_nonneg (z.re ^ 2 + (8) ^ 2)
    have h7 : (2 - z.re) ≥ 0 := by linarith [h5, h6]
    have h8 : (Real.sqrt (z.re ^ 2 + (8) ^ 2)) ^ 2 = (2 - z.re) ^ 2 := by 
      rw [h5]
    have h9 : (Real.sqrt (z.re ^ 2 + (8) ^ 2)) ^ 2 = z.re ^ 2 + (8) ^ 2 := Real.sq_sqrt (show 0 ≤ z.re ^ 2 + (8 : ℝ) ^ 2 by positivity)
    have eq4 : z.re ^ 2 + (8 : ℝ) ^ 2 = (2 - z.re) ^ 2 := by
      linarith [h8, h9]
    nlinarith
  have h3 : Complex.abs z = (17 : ℝ) := by 
    rw [h2]
    rw [show z.re = (-15 : ℝ) by linarith [h4]]
    rw [show z.im = (8 : ℝ) by linarith [h1]]
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
  rw [h3]
  all_goals norm_num