import Mathlib

open Complex
theorem algebra_273928 (z : ℂ) (hz : Complex.abs z = 1) :
    (z ^ 2).re + (z ^ 2).im ≤ Real.sqrt 2 ∧
    ∃ z : ℂ, Complex.abs z = 1 ∧ (z ^ 2).re + (z ^ 2).im = Real.sqrt 2 := by
  have h1 : z.re ^ 2 + z.im ^ 2 = 1 := by
    have h_abs : Complex.abs z = Real.sqrt (z.re ^ 2 + z.im ^ 2) := by
      simp [Complex.abs, Complex.normSq]
      all_goals ring
    rw [h_abs] at hz
    have h_eq : Real.sqrt (z.re ^ 2 + z.im ^ 2) = 1 := hz
    have h2 : z.re ^ 2 + z.im ^ 2 = 1 := by
      calc
        z.re ^ 2 + z.im ^ 2 = (Real.sqrt (z.re ^ 2 + z.im ^ 2)) ^ 2 := by rw [Real.sq_sqrt]; positivity
        _ = (1 : ℝ) ^ 2 := by rw [h_eq]
        _ = (1 : ℝ) := by norm_num
    exact h2
  have h2 : (z ^ 2).re = z.re ^ 2 - z.im ^ 2 := by
    simp [pow_two, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
  have h3 : (z ^ 2).im = 2 * z.re * z.im := by
    simp [pow_two, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    all_goals ring
  have h4 : (z ^ 2).re + (z ^ 2).im ≤ Real.sqrt 2 := by
    rw [h2, h3]
    have h7 : z.re ^ 2 + z.im ^ 2 = 1 := h1
    nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num),
      sq_nonneg (z.re ^ 2 - z.im ^ 2 - 2 * z.re * z.im), sq_nonneg (z.re - z.im), sq_nonneg (z.re + z.im),
      sq_nonneg (z.re ^ 2 + z.im ^ 2 - 1), sq_nonneg (z.re ^ 2 - z.im ^ 2 - 1), sq_nonneg (2 * z.re * z.im),
      sq_nonneg (z.re ^ 2 - z.im ^ 2 - 2 * z.re * z.im), sq_nonneg (z.re ^ 2 - z.im ^ 2 + 2 * z.re * z.im - Real.sqrt 2),
      Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  have h8 : ∃ z : ℂ, Complex.abs z = 1 ∧ (z ^ 2).re + (z ^ 2).im = Real.sqrt 2 := by
    use Complex.exp (Complex.I * (Real.pi / 8))
    constructor
    · -- Show that |z| = 1
      have h9 : Complex.abs (Complex.exp (Complex.I * (Real.pi / 8))) = 1 := by
        simp [Complex.abs_exp]
      exact h9
    · -- Show that (z^2).re + (z^2).im = Real.sqrt 2
      have h10 : (Complex.exp (Complex.I * (Real.pi / 8)) ^ 2).re = Real.cos (2 * (Real.pi / 8)) := by
        have h11 : Complex.exp (Complex.I * (Real.pi / 8)) ^ 2 = Complex.exp (2 * Complex.I * (Real.pi / 8)) := by
          rw [← Complex.exp_nat_mul]
          all_goals ring
        rw [h11]
        simp [Complex.exp_re, mul_comm]
      have h12 : (Complex.exp (Complex.I * (Real.pi / 8)) ^ 2).im = Real.sin (2 * (Real.pi / 8)) := by
        have h11 : Complex.exp (Complex.I * (Real.pi / 8)) ^ 2 = Complex.exp (2 * Complex.I * (Real.pi / 8)) := by
          rw [← Complex.exp_nat_mul]
          all_goals ring
        rw [h11]
        simp [Complex.exp_im, mul_comm]
      rw [h10, h12]
      have h14 : Real.cos (2 * (Real.pi / 8)) = Real.cos (Real.pi / 4) := by ring
      have h15 : Real.sin (2 * (Real.pi / 8)) = Real.sin (Real.pi / 4) := by ring
      rw [h14, h15]
      have h13 : Real.cos (Real.pi / 4) + Real.sin (Real.pi / 4) = Real.sqrt 2 := by
        have h17 : Real.cos (Real.pi / 4) = Real.sqrt 2 / 2 := Real.cos_pi_div_four
        have h18 : Real.sin (Real.pi / 4) = Real.sqrt 2 / 2 := Real.sin_pi_div_four
        linarith
      linarith
  constructor
  · exact h4
  · exact h8