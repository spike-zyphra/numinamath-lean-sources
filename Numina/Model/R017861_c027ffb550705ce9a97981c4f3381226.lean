import Mathlib

theorem algebra_10142 {z : ℂ} (hz : (1 + .I) * z = Complex.abs (1 + .I) ^ 2) :
    (z : ℂ).im = -1 := by
  have h_abs : Complex.abs (1 + Complex.I) = Real.sqrt 2 := by
    simp [Complex.abs, Complex.normSq]
    <;> ring_nf <;> norm_num
  
  have h_abs2 : (Complex.abs (1 + Complex.I) : ℝ) ^ 2 = 2 := by
    rw [h_abs]
    rw [Real.sq_sqrt]
    all_goals norm_num
  
  have eq1 := congr_arg (λ w : ℂ => w.re) hz
  have eq2 := congr_arg (λ w : ℂ => w.im) hz
  
  simp [Complex.add_re, Complex.mul_re, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.normSq, h_abs, Real.sq_sqrt, pow_two] at eq1 eq2
  
  norm_num [h_abs, pow_two, Complex.abs, Complex.normSq] at eq1 eq2 ⊢
  ring_nf at eq1 eq2 ⊢
  norm_num at eq1 eq2 ⊢
  
  linarith