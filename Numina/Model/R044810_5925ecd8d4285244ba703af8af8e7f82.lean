import Mathlib

theorem algebra_11520 {z : ℂ} (hz : z^2 = 24 - 32 * .I) : Complex.abs z = 2 * Real.sqrt 10 := by
  have eq1 := congr_arg Complex.re hz
  have eq2 := congr_arg Complex.im hz
  simp [pow_two, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im] at eq1 eq2
  have h1 : z.re^2 - z.im^2 = 24 := by linarith [eq1, eq2]
  have h2 : 2 * z.re * z.im = -32 := by linarith [eq1, eq2]
  have h3 : z.re * z.im = -16 := by
    nlinarith 
  have h4 : z.re ^2 + z.im ^2 = 40 := by 
    have eq3 : z.re ^2 - z.im ^2 = 24 := h1
    have eq4 : z.re * z.im = -16 := h3
    have eq5 : z.re ^2 * z.im ^2 = 256 := by 
      nlinarith [eq4]
    have eq6 : z.im ^2 = 8 := by
      nlinarith [eq3, eq5]
    have eq7 : z.re ^2 = 32 := by 
      nlinarith [eq3, eq6]
    nlinarith [eq6, eq7]
  have h5 : Complex.abs z = Real.sqrt (z.re ^2 + z.im ^2) := by 
    simp [Complex.abs, Complex.normSq]
    <;> ring 
  rw [h5]
  rw [show z.re ^2 + z.im ^2 = (40 : ℝ) by linarith [h4]]
  have h6 : Real.sqrt (40 : ℝ) = 2 * Real.sqrt 10 := by 
    rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
    <;> ring_nf <;> norm_num 
  rw [show (40 : ℝ) = (40 : ℝ) by norm_num]
  rw [h6]
  all_goals norm_num