import Mathlib

theorem algebra_12396 {z : ℂ} (hz : z ^ 2 + Complex.abs z ^ 2 = 3 - 5 * .I) :
    Complex.abs z ^ 2 = 17 / 3 := by
  have eq1 : (z ^ 2 + Complex.abs z ^ 2).re = (3 - 5 * Complex.I).re := by 
    rw [hz]
  have eq2 : (z ^ 2 + Complex.abs z ^ 2).im = (3 - 5 * Complex.I).im := by 
    rw [hz]
  simp [pow_two, Complex.add_re, Complex.ofReal_re, Complex.I_re, Complex.add_im, Complex.ofReal_im, Complex.I_im, Complex.abs, Complex.normSq] at eq1 eq2 
  ring_nf at eq1 eq2
  have eq3 : z.re ^ 2 = 3 / 2 := by 
    have h_eq : √(z.re ^ 2 + z.im ^ 2) ^ 2 = z.re ^ 2 + z.im ^ 2 := by
      rw [Real.sq_sqrt]
      positivity
    have eq6 : z.re ^ 2 - z.im ^ 2 + (z.re ^ 2 + z.im ^ 2) = 3 := by
      nlinarith [eq1, h_eq]
    nlinarith
  have h1 : z.re ^ 2 = 3 / 2 := eq3
  have h2 : z.re * z.im = -5 / 2 := by
    nlinarith
  have h3 : z.re ≠ 0 := by 
    by_contra h
    have h4 : z.re ^ 2 = 0 := by
      rw [h]
      norm_num
    nlinarith [h1, h4]
  have h6 : z.im ^ 2 = 25 / 6 := by
    have h7 : z.re * z.im = -5 / 2 := h2
    have h8 : z.re ^ 2 = 3 / 2 := h1
    have h9 : z.re ≠ 0 := h3
    have h10 : z.im = (-5 / 2) / z.re := by
      have h6 : z.re * z.im = -5 / 2 := h2
      have h9 : z.re ≠ 0 := h3
      field_simp [h9] at h6 ⊢
      nlinarith
    have h11 : z.im ^ 2 = ((-5 / 2) / z.re) ^ 2 := by 
      rw [h10]
    have h13 : z.re ^ 2 = 3 / 2 := h1
    rw [h11]
    field_simp [h3]
    <;> nlinarith
  have h5 : Complex.abs z ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    have h6 : Complex.abs z = Real.sqrt (z.re ^ 2 + z.im ^ 2) := by
      simp [Complex.abs, Complex.normSq]
      <;> ring_nf
    rw [h6]
    rw [Real.sq_sqrt (by positivity)]
  rw [h5]
  nlinarith [h1, h6]