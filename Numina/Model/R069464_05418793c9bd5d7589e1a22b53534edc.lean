import Mathlib

theorem algebra_103584 (z : ℂ) (hz : Complex.abs (z - 2 + Complex.I) = 5) (hzz : (z * (1 + Complex.I)).re = 2) :
    z = 5 + 3 * Complex.I ∨ z = -2 - 4 * Complex.I := by
  have eq1 : Complex.abs (z - 2 + Complex.I) = Real.sqrt ((z.re - 2) ^ 2 + (z.im + 1) ^ 2) := by
    simp [Complex.abs, Complex.normSq, Complex.re, Complex.im]
    <;> ring_nf
    <;> simp
    <;> ring_nf <;> simp [mul_add, pow_two]
    all_goals ring_nf <;> simp
    <;> ring_nf <;> norm_num
    all_goals ring_nf <;> simp
    <;> ring_nf
  rw [eq1] at hz
  have h3 : (z.re - 2) ^ 2 + (z.im + 1) ^ 2 = 25 := by 
    calc 
      (z.re - 2) ^ 2 + (z.im + 1) ^ 2 = (Real.sqrt ((z.re - 2) ^ 2 + (z.im + 1) ^ 2)) ^ 2 := by rw [Real.sq_sqrt]; positivity
      _ = 5 ^ 2 := by rw [hz]
      _ = 25 := by norm_num
  have h4 : (z.re - z.im) = 2 := by 
    have h5 : (z * (1 + Complex.I)).re = z.re - z.im := by 
      simp [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re, Complex.I_im, 
            Complex.mul_im, Complex.add_im]
      <;> ring_nf 
      <;> simp [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
      all_goals ring_nf
    rw [h5] at hzz
    linarith
  have h5 : z.re = z.im + 2 := by linarith
  rw [h5] at h3
  have h6 : (z.im - 3) * (z.im + 4) = 0 := by 
    nlinarith
  cases' (mul_eq_zero.mp h6) with h7 h8
  · -- Case where `z.im = 3`
    have him : z.im = 3 := by linarith
    have himre : z.re = 5 := by 
      linarith [h5, him]
    have h8 : z = 5 + 3 * Complex.I := by
      simp [Complex.ext_iff, himre, him]
      all_goals tauto
    left
    exact h8
  · -- Case where `z.im = -4`
    have him : z.im = -4 := by linarith
    have himre : z.re = -2 := by 
      linarith [h5, him]
    have h8 : z = -2 - 4 * Complex.I := by
      simp [Complex.ext_iff, himre, him]
      all_goals tauto
    right
    exact h8