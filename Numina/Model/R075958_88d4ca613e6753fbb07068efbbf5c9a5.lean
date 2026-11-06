import Mathlib

theorem algebra_21191 {z : ℂ} (hz : z + Complex.abs z = 2 + 8 * .I) :
    z = -15 + 8 * .I := by 

  have hzr : z.re + Complex.abs z = 2 := by 
    have h := congr_arg Complex.re hz
    simp [Complex.add_re, Complex.ofReal_re, Complex.I_re, pow_two] at h ⊢ 
    linarith

  have hzi : z.im = 8 := by 
    have h := congr_arg Complex.im hz
    simp [Complex.add_im, Complex.ofReal_im, Complex.I_im] at h ⊢ 
    linarith

  have hzre : z.re = -15 := by

    have h_abs : Complex.abs z = Real.sqrt (z.re ^ 2 + z.im ^ 2) := by 
      have h_abs' : Complex.abs z = Real.sqrt (z.re^2 + z.im^2) := by
        simp [Complex.abs, Complex.normSq]
        <;> ring_nf <;> simp [pow_two]
        <;> ring
      exact h_abs'
    
    rw [h_abs] at hzr 
    rw [hzi] at hzr

    -- Solving the equation $z.re + \sqrt(z.re^2 + 64) = 2$ 
    -- Let $a = re(z)$
    -- $a + \sqrt(a^2 + 64) = 2$
    -- $\sqrt(a^2 + 64) = 2 - a$
    -- Square both sides: $a^2 + 64 = 4 - 4*a + a^2$
    -- $64 = 4 - 4*a$
    -- $60 = -4*a$
    -- $a = -15$
  
    have h_eq : z.re + Real.sqrt (z.re ^ 2 + (8 : ℝ) ^ 2) = 2 := by 
      linarith
  
    have h_eq2 : Real.sqrt (z.re ^ 2 + (8 : ℝ) ^ 2) = 2 - z.re := by 
      linarith [h_eq]

    have h_eq3 : (z.re ^ 2 + (8 : ℝ) ^ 2) = (2 - z.re) ^ 2 := by
      calc
        z.re ^ 2 + (8 : ℝ) ^ 2 = (Real.sqrt (z.re ^ 2 + (8 : ℝ) ^ 2)) ^ 2 := by 
          rw [Real.sq_sqrt]
          positivity
        _ = (2 - z.re) ^ 2 := by 
          rw [h_eq2]

    -- Solving the polynomial equation. Expanding both sides:
    -- z.re^2 + 64 = 4 - 4*z.re + z.re^2
    -- 64 = 4 - 4*z.re
    -- 60 = -4*z.re
    -- z.re = -15

    nlinarith [Real.sqrt_nonneg (z.re ^ 2 + (8 : ℝ) ^ 2), Real.sq_sqrt (show (z.re ^ 2 + (8 : ℝ) ^ 2) ≥ 0 by positivity)]

  simp [Complex.ext_iff, hzre, hzi]
  <;> try linarith
  <;> try positivity