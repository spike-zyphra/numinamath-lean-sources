import Mathlib

theorem algebra_220185 (z : ℂ) (h : Complex.abs (z ^ 2 + 1) = 2 * Complex.abs (z + 1)) :
    Complex.abs z ≤ Real.sqrt 7 := by
  have h1 : Complex.abs (z ^ 2 + 1) = Real.sqrt ((z ^ 2 + 1).re ^ 2 + (z ^ 2 + 1).im ^ 2) := by
    simp [Complex.abs, Complex.normSq]
    <;> ring_nf
  have h2 : Complex.abs (z + 1) = Real.sqrt ((z + 1).re ^ 2 + (z + 1).im ^ 2) := by
    simp [Complex.abs, Complex.normSq]
    <;> ring_nf
  rw [h1, h2] at h

  have h3 : (z ^ 2 + 1).re ^ 2 + (z ^ 2 + 1).im ^ 2 = 4 * ((z + 1).re ^ 2 + (z + 1).im ^ 2) := by
    have h4 : Real.sqrt ((z ^ 2 + 1).re ^ 2 + (z ^ 2 + 1).im ^ 2) = 2 * Real.sqrt ((z + 1).re ^ 2 + (z + 1).im ^ 2) := h
    have h5 : (Real.sqrt ((z ^ 2 + 1).re ^ 2 + (z ^ 2 + 1).im ^ 2)) ^ 2 = (2 * Real.sqrt ((z + 1).re ^ 2 + (z + 1).im ^ 2)) ^ 2 := by
      rw [h4]
    have h6 : (Real.sqrt ((z ^ 2 + 1).re ^ 2 + (z ^ 2 + 1).im ^ 2)) ^ 2 = (z ^ 2 + 1).re ^ 2 + (z ^ 2 + 1).im ^ 2 := by
      rw [Real.sq_sqrt]
      positivity
    have h7 : (2 * Real.sqrt ((z + 1).re ^ 2 + (z + 1).im ^ 2)) ^ 2 = 4 * ((z + 1).re ^ 2 + (z + 1).im ^ 2) := by
      calc
        (2 * Real.sqrt ((z + 1).re ^ 2 + (z + 1).im ^ 2)) ^ 2
          = 4 * (Real.sqrt ((z + 1).re ^ 2 + (z + 1).im ^ 2) ^ 2) := by
            ring_nf
            <;> norm_num
            <;> ring_nf
        _ = 4 * ((z + 1).re ^ 2 + (z + 1).im ^ 2) := by
          have h8 : Real.sqrt ((z + 1).re ^ 2 + (z + 1).im ^ 2) ^ 2 = (z + 1).re ^ 2 + (z + 1).im ^ 2 := by
            rw [Real.sq_sqrt]
            positivity
          rw [h8]
    rw [h6] at h5
    rw [h7] at h5
    nlinarith

  have eq1 : (z ^ 2 + 1).re = z.re ^ 2 - z.im ^ 2 + 1 := by
    simp [pow_two, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.I_re, Complex.I_im]
    <;> ring_nf
    <;> simp [Complex.I_re, Complex.I_im]

  have eq2 : (z ^ 2 + 1).im = 2 * z.re * z.im := by
    simp [pow_two, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.I_re, Complex.I_im]
    <;> ring_nf
    <;> simp [Complex.I_re, Complex.I_im]

  have eq3 : (z + 1).re = z.re + 1 := by
    simp [Complex.add_re, Complex.ofReal_re, Complex.I_re]

  have eq4 : (z + 1).im = z.im := by
    simp [Complex.add_im, Complex.ofReal_im, Complex.I_im]

  rw [eq1, eq2, eq3, eq4] at h3

  have h4' : z.re ^ 2 + z.im ^ 2 ≤ 7 := by
    nlinarith [sq_nonneg (z.re - z.im), sq_nonneg (z.re + z.im), sq_nonneg (z.re - 1), sq_nonneg (z.im - 1), sq_nonneg (z.re ^ 2 - z.im ^ 2), sq_nonneg (z.re * z.im)]

  have h5 : Complex.abs z = Real.sqrt (z.re ^ 2 + z.im ^ 2) := by
    simp [Complex.abs, Complex.normSq]
    <;> ring_nf

  rw [h5]
  have h6 : Real.sqrt (z.re ^ 2 + z.im ^ 2) ≤ Real.sqrt (7 : ℝ) := Real.sqrt_le_sqrt (h4')
  linarith