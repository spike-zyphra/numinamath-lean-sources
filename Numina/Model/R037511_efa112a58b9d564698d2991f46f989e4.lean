import Mathlib

theorem algebra_222501 (z : ℂ) (hz : Complex.abs (z + 1) < 1 / Real.sqrt 2) :
    Complex.abs (z^2 + 1) ≥ 1 := by
  have h1 : Complex.abs (z + 1) = Real.sqrt ((z.re + 1) ^ 2 + (z.im) ^ 2) := by
    simp [Complex.abs, Complex.normSq]
    <;> ring
  rw [h1] at hz
  have h2 : (z.re + 1) ^ 2 + (z.im) ^ 2 < (1 / 2 : ℝ) := by
    have h4 : 0 < Real.sqrt 2 := by positivity
    have h5 : (1 / Real.sqrt 2) ^ 2 = (1 / 2 : ℝ) := by
      field_simp
    have h6 : Real.sqrt ((z.re + 1) ^ 2 + (z.im) ^ 2) < (1 / Real.sqrt 2) := hz
    have h7 : (Real.sqrt ((z.re + 1) ^ 2 + (z.im) ^ 2)) ^ 2 < (1 / Real.sqrt 2) ^ 2 := by nlinarith [Real.sqrt_nonneg ((z.re + 1) ^ 2 + (z.im) ^ 2), (show (0 : ℝ) < (1 / Real.sqrt 2) by positivity)]
    rw [show (Real.sqrt ((z.re + 1) ^ 2 + (z.im) ^ 2)) ^ 2 = (z.re + 1) ^ 2 + (z.im) ^ 2 by exact Real.sq_sqrt (show (z.re + 1) ^ 2 + (z.im) ^ 2 ≥ 0 by positivity)] at h7
    rw [h5] at h7
    linarith
  have h3 : Complex.abs (z ^ 2 + 1) = Real.sqrt ((z.re ^ 2 - z.im ^ 2 + 1) ^ 2 + (2 * z.re * z.im) ^ 2) := by
    simp [Complex.abs, Complex.normSq, pow_two, pow_succ, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_add, add_mul]
    <;> ring_nf
  rw [h3]
  have h4 : (z.re ^ 2 - z.im ^ 2 + 1) ^ 2 + (2 * z.re * z.im) ^ 2 ≥ 1 := by
    nlinarith [sq_nonneg (z.re + 1), sq_nonneg (z.im), sq_nonneg (z.re - z.im), sq_nonneg (z.re + z.im), sq_nonneg (z.re^2 - 1/2), sq_nonneg (z.im^2 - 1/2), mul_nonneg (show (0 : ℝ) ≤ z.re ^ 2 by positivity) (show (0 : ℝ) ≤ z.im ^ 2 by positivity), mul_nonneg (show (0 : ℝ) ≤ z.re ^ 2 by positivity) (show (0 : ℝ) ≤ (1/4 : ℝ) by positivity), mul_nonneg (show (0 : ℝ) ≤ z.im ^ 2 by positivity) (show (0 : ℝ) ≤ (1/4 : ℝ) by positivity) ]
  have h5 : Real.sqrt ((z.re ^ 2 - z.im ^ 2 + 1) ^ 2 + (2 * z.re * z.im) ^ 2) ≥ Real.sqrt (1 : ℝ) := Real.sqrt_le_sqrt (by linarith)
  have h6 : Real.sqrt (1 : ℝ) = 1 := Real.sqrt_eq_cases.mpr (by norm_num)
  linarith [h6, h5]