import Mathlib

theorem algebra_12385 {z : ℂ} (hz : Complex.abs z * (3 * z + 2 * Complex.I) = 2 * (Complex.I * z - 6)) :
    Complex.abs z = 2 := by
  have eq1 := congr_arg Complex.re hz
  have eq2 := congr_arg Complex.im hz

  simp [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, 
        Complex.I_re, Complex.I_im, Complex.add_im, Complex.mul_re, Complex.mul_im] at eq1 eq2
  -- Now we have equations about real and imaginary parts
  -- eq1: ↑(Complex.abs z) * (3 * z.re) = 2 * (-z.im - 6)
  -- eq2: ↑(Complex.abs z) * (3 * z.im + 2) = 2 * z.re
  
  have eq5 : (Complex.abs z) * 3 * z.re = -12 - 2 * z.im := by
    nlinarith

  have eq6 : (Complex.abs z) * (3 * z.im + 2) = 2 * z.re := by
    nlinarith
  
  have h7 : Complex.abs z ≥ 0 := by 
    have h8 : Complex.abs z = Real.sqrt (z.re^2 + z.im^2) := by
      simp [Complex.abs, Complex.normSq]
      <;> ring_nf <;> simp
      <;> ring 
    rw [h8]
    apply Real.sqrt_nonneg
  
  -- Solving
  have h8 : z.re ^ 2 + z.im ^ 2 = (Complex.abs z) ^ 2 := by
    have h5 : Complex.abs z = Real.sqrt (z.re ^ 2 + z.im ^ 2) := by 
      simp [Complex.abs, Complex.normSq]
      <;> ring_nf <;> simp
      <;> ring 
    have h8 : (Real.sqrt (z.re ^ 2 + z.im ^ 2)) ^ 2 = z.re ^ 2 + z.im ^ 2 := by
      rw [Real.sq_sqrt]
      positivity
    rw [show Real.sqrt (z.re ^ 2 + z.im ^ 2) = Complex.abs z by linarith [h5]] at h8
    nlinarith
  
  have h10 : Complex.abs z = 2 := by
    by_cases h12 : Complex.abs z = 0
    · -- If Complex.abs z = 0, reach contradiction
      have eq5' : (Complex.abs z) * 3 * z.re = -12 - 2 * z.im := by
        nlinarith 
      rw [h12] at eq5'
      nlinarith 

    · -- else case
      -- Now we need the square expressions to solve
      have h14 : (Complex.abs z) ^ 2 = 4 := by 
        nlinarith [sq_nonneg (z.re * 25), sq_nonneg (z.im * 25), sq_nonneg (Complex.abs z - 2), sq_nonneg (z.re + 8 / 5), sq_nonneg (z.im + 6 / 5), 
                  mul_nonneg (show (0 : ℝ) ≤ Complex.abs z by nlinarith [h7]) (show (0 : ℝ) ≤ Complex.abs z by nlinarith [h7])]
      have h9 : Complex.abs z = 2 := by
        nlinarith [h14, show Complex.abs z ≥ 0 by exact h7]
      assumption
  
  exact h10