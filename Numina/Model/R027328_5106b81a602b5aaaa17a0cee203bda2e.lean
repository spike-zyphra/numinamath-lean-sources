import Mathlib

theorem algebra_11991 {z : ℂ} (hz : z + Complex.abs z = 2 + Complex.I) :
    z = 3 / 4 + Complex.I := by 
  have h1 : z.im = 1 := by
    have eq1 := congr_arg Complex.im hz
    simp [Complex.add_im, Complex.ofReal_im, Complex.I_im] at eq1
    linarith
  have h2 : z.re = 3 / 4 := by
    have eq2 := congr_arg Complex.re hz
    have h_mod : Complex.abs z = Real.sqrt (z.re ^ 2 + z.im ^ 2) := by
      simp [Complex.abs, Complex.normSq, h1]
      <;> ring_nf <;> simp [Complex.ext_iff]
      <;> ring_nf <;> simp [pow_two]
      <;> ring_nf
    rw [h_mod] at eq2
    simp [Complex.add_re, Complex.ofReal_re, Complex.I_re, h1] at eq2 
    -- We have the equation z.re + Real.sqrt (z.re ^ 2 + 1) = 2
    -- Solving for z.re
    have eq2' : Real.sqrt (z.re ^ 2 + 1) = 2 - z.re := by linarith 
    have eq2_pos : 0 ≤ Real.sqrt (z.re ^ 2 + 1) := Real.sqrt_nonneg (z.re ^ 2 + 1)
    have eq2_neg : 2 - z.re ≥ 0 := by linarith [eq2_pos, eq2']
    have eq2_sq : z.re ^ 2 + 1 = (2 - z.re) ^ 2 := by
      calc
        z.re ^ 2 + 1 = (Real.sqrt (z.re ^ 2 + 1)) ^ 2 := by
          rw [Real.sq_sqrt]
          positivity 
        _ = (2 - z.re) ^ 2 := by
          rw [eq2']
    have eq2_expanded : z.re ^ 2 + 1 = 4 - 4 * z.re + z.re ^ 2 := by
      nlinarith 
    have eq2_simplified : 1 = 4 - 4 * z.re := by
      nlinarith 
    nlinarith 
  rw [Complex.ext_iff]
  simp [h2, h1]
  all_goals norm_num
  all_goals assumption