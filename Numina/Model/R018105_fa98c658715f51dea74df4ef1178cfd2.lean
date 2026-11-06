import Mathlib

theorem algebra_208193 {z : ℂ} (hz : z + Complex.abs z = 2 + 8 * .I) :
    Complex.abs z ^ 2 = 289 := by
  have eq1 := congr_arg Complex.re hz
  have eq2 := congr_arg Complex.im hz
  simp [Complex.add_re, Complex.ofReal_re, Complex.I_re, Complex.add_im, Complex.ofReal_im, Complex.I_im] at eq1 eq2
  have h1 : z.im = 8 := by linarith [eq2]
  have h2 : z.re + Complex.abs z = 2 := by linarith [eq1]
  have h3 : Complex.abs z = Real.sqrt ((z.re) ^ 2 + z.im ^ 2) := by
    simp [Complex.abs, Complex.normSq]
    <;> ring_nf
  rw [h1] at h3
  have h4 : Complex.abs z = Real.sqrt (z.re ^ 2 + 8 ^ 2) := by
    rw [h3]
    all_goals try norm_num
  have h5 : z.re + Real.sqrt (z.re ^ 2 + 8 ^ 2) = 2 := by 
    rw [h4] at h2
    linarith
  have h6 : Real.sqrt (z.re ^ 2 + 8 ^ 2) = 2 - z.re := by 
    linarith [h5]
  have h7 : z.re ^ 2 + 8 ^ 2 = (2 - z.re) ^ 2 := by
    calc
      z.re ^ 2 + 8 ^ 2 = (Real.sqrt (z.re ^ 2 + 8 ^ 2)) ^ 2 := by
        rw [Real.sq_sqrt]
        positivity
      _ = (2 - z.re) ^ 2 := by 
        rw [h6]
  have h8 : z.re = -15 := by
    nlinarith
  have h9 : Complex.abs z = 17 := by
    rw [h4]
    rw [h8]
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
  rw [h9]
  all_goals norm_num