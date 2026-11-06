import Mathlib

theorem algebra_269672 {z : ℂ} (hz : Complex.abs z * (3 * z + 2 * .I) = 2 * (.I * z - 6)) :
    Complex.abs z = 2 := by 
  have eq1 := congr_arg Complex.re hz 
  have eq2 := congr_arg Complex.im hz 
  simp [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, 
        Complex.I_re, Complex.I_im] at eq1 eq2
  have h1 : Complex.abs z ≥ 0 := by positivity 
  have eq3 : (Complex.abs z) ^ 2 = z.re ^ 2 + z.im ^ 2 := by 
    have h : Complex.abs z = Real.sqrt (z.re ^ 2 + z.im ^ 2) := by 
      simp [Complex.abs, Complex.normSq]
      <;> ring_nf
    rw [h]
    rw [Real.sq_sqrt (by positivity)]
  nlinarith [sq_nonneg (Complex.abs z - 2), sq_nonneg (z.re + 16 / 10), sq_nonneg (z.im + 12 / 10), 
          Real.sqrt_nonneg (z.re ^ 2 + z.im ^ 2)]