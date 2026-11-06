import Mathlib

theorem algebra_9380 {z : ℂ} (hz : z + Complex.abs z * .I = 3 + 9 * .I) :
    z = 3 + 4 * .I := by
  have h1 : z.re = 3 := by 
    have eq1 := congr_arg Complex.re hz
    simp [Complex.add_re, Complex.ofReal_re, Complex.I_re] at eq1 
    linarith
  have eq2 := congr_arg Complex.im hz
  simp [Complex.add_im, Complex.ofReal_im, Complex.I_im] at eq2
  have h2 : z.im = 4 := by
    have h3 : Complex.abs z = Real.sqrt (z.re^2 + z.im^2) := by 
      simp [Complex.abs, Complex.normSq]
      <;> ring_nf
    rw [h3] at eq2 
    rw [show z.re = 3 by linarith [h1] ] at eq2 
    have h4 : z.im = 4 := by 
      nlinarith [Real.sqrt_nonneg (3^2 + z.im^2), Real.sq_sqrt (show 0 ≤ (3^2 + z.im^2 : ℝ) by nlinarith)]
    linarith [h4]
  have h5 : z = 3 + 4 * Complex.I := by 
    simp [Complex.ext_iff, h1, h2]
  exact h5