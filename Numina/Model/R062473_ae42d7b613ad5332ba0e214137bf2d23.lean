import Mathlib

theorem algebra_284446 (z : ℂ) (hz : Complex.abs z - 1 ≤ 0) :
    Complex.abs (z ^ 3 - 3 * z - 2) ≤ 3 * Real.sqrt 3 := by
  have h1 : Complex.abs z ≤ 1 := by
    linarith
  have h2 : Complex.abs (z ^ 3 - 3 * z - 2) ≤ 3 * Real.sqrt 3 := by 
    have h3 : z.re^2 + z.im^2 ≤ (1 : ℝ) := by
      have h_abs : Complex.abs z ≤ 1 := by 
        linarith
      have h_abs_eq : Complex.abs z = Real.sqrt (z.re^2 + z.im^2) := by
        simp [Complex.abs, Complex.normSq]
        <;> ring
        <;> norm_num
        <;> ring
      rw [h_abs_eq] at h_abs
      have h4 : z.re^2 + z.im^2 ≤ (1 : ℝ) := by
        have h5 : Real.sqrt (z.re^2 + z.im^2) ≤ (1 : ℝ) := h_abs
        have h6 : (Real.sqrt (z.re^2 + z.im^2)) ^ 2 ≤ (1 : ℝ) ^ 2 := by nlinarith [Real.sqrt_nonneg (z.re^2 + z.im^2), h5]
        rw [Real.sq_sqrt (by positivity)] at h6
        nlinarith
      linarith
    have h4 : Complex.abs (z ^ 3 - 3 * z - 2) = Real.sqrt ((z.re^3 - 3 * z.re * z.im^2 - 3 * z.re - 2) ^ 2 + (3 * z.re^2 * z.im - z.im^3 - 3 * z.im) ^ 2) := by
      simp [Complex.abs, Complex.normSq, pow_two, Complex.ext_iff, pow_three]
      ring_nf
      <;> simp [pow_two, mul_add, add_mul,Complex.I_mul_I]
      <;> ring_nf
      <;> norm_num
    rw [h4]
    have h5 : (z.re^3 - 3 * z.re * z.im^2 - 3 * z.re - 2) ^ 2 + (3 * z.re^2 * z.im - z.im^3 - 3 * z.im) ^ 2 ≤ (3 * Real.sqrt 3) ^ 2 := by
      nlinarith [sq_nonneg (z.re - 1 / 2), sq_nonneg (z.re + 1 / 2), sq_nonneg (z.im ^ 2 - (3 / 4)), sq_nonneg (z.re ^ 2 + z.re - 1), sq_nonneg (z.re - 1), sq_nonneg (z.re + 1), sq_nonneg (z.re * 3 - 1), sq_nonneg (z.re - 1 / 2), sq_nonneg (z.re + 1 / 2), sq_nonneg (z.re ^ 2 + z.re - 1), sq_nonneg (z.re ^ 2 - z.re), sq_nonneg (z.re - 2), sq_nonneg (z.re + 2), sq_nonneg (z.re - 1 / 2), 
        Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), mul_nonneg (Real.sqrt_nonneg 3) (Real.sqrt_nonneg 3), h3]
    have h8 : Real.sqrt ((z.re^3 - 3 * z.re * z.im^2 - 3 * z.re - 2) ^ 2 + (3 * z.re^2 * z.im - z.im^3 - 3 * z.im) ^ 2) ≤ 3 * Real.sqrt 3 := by
      have h7 : Real.sqrt ((z.re^3 - 3 * z.re * z.im^2 - 3 * z.re - 2) ^ 2 + (3 * z.re^2 * z.im - z.im^3 - 3 * z.im) ^ 2) ≤ Real.sqrt ((3 * Real.sqrt 3) ^ 2) := Real.sqrt_le_sqrt (by linarith [h5])
      have h8 : Real.sqrt ((3 * Real.sqrt 3) ^ 2) = 3 * Real.sqrt 3 := by
        rw [Real.sqrt_sq (by positivity)]
      linarith [h7, h8]
    linarith [h8]
  exact h2