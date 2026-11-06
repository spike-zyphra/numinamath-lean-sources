import Mathlib

theorem algebra_12164 :
    IsGreatest {x | ∃ z : ℂ, x = Complex.abs (z ^ 3 - 3 * z - 2) ∧ Complex.abs z = 1} (3 * Real.sqrt 3) := by
  constructor
  · -- Show that 3 * sqrt(3) is achievable.
    use 1 / 2 + Complex.I * Real.sqrt 3 / 2
    constructor
    · -- Show that the modulus is equal to 3 * sqrt(3)
      have h1 : (1 / 2 + Complex.I * Real.sqrt 3 / 2 : ℂ) ^ 3 - 3 * (1 / 2 + Complex.I * Real.sqrt 3 / 2 : ℂ) - 2 = (-9 / 2 - Complex.I * 3 * Real.sqrt 3 / 2) := by
        simp [pow_three, Complex.ext_iff, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, mul_add, add_mul]
        field_simp
        ring_nf
        <;> norm_num [Real.sqrt_sq]
        <;> ring
      rw [h1]
      have h2 : Complex.abs ((-9 / 2 - Complex.I * 3 * Real.sqrt 3 / 2) : ℂ) = Real.sqrt ((-9 / 2 : ℝ) ^ 2 + (3 * Real.sqrt 3 / 2 : ℝ) ^ 2) := by
        simp [Complex.abs, Complex.normSq]
        <;> ring_nf
      rw [h2]
      have h3 : Real.sqrt ((-9 / 2 : ℝ) ^ 2 + (3 * Real.sqrt 3 / 2 : ℝ) ^ 2) = 3 * Real.sqrt 3 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num [mul_pow, pow_two, Real.sq_sqrt]
        <;> ring_nf <;> norm_num [Real.sq_sqrt]
      rw [h3]
    · -- Show that the modulus is 1
      simp [Complex.abs, Complex.normSq]
      <;> ring_nf
      <;> norm_num [Real.sqrt_sq]
  · -- Show that 3 * sqrt(3) is the greatest
    intro x hx
    rcases hx with ⟨z, h1, h2⟩
    have h_abs : Complex.abs z = 1 := h2
    have h3 : z.re ^ 2 + z.im ^ 2 = 1 := by
      have h_abs' : Complex.abs z = 1 := h2
      have h4 : Complex.abs z = Real.sqrt (z.re ^ 2 + z.im ^ 2) := by
        simp [Complex.abs, Complex.normSq]
        <;> ring_nf
      rw [h4] at h_abs
      have h5 : Real.sqrt (z.re ^ 2 + z.im ^ 2) = 1 := h_abs
      have h6 : z.re ^ 2 + z.im ^ 2 = 1 := by
        calc
          z.re ^ 2 + z.im ^ 2 = (Real.sqrt (z.re ^ 2 + z.im ^ 2)) ^ 2 := by
            rw [Real.sq_sqrt]
            positivity
          _ = 1 ^ 2 := by rw [h5]
          _ = 1 := by norm_num
      exact h6
    rw [h1]
    have h4 : Complex.abs (z ^ 3 - 3 * z - 2) ≤ 3 * Real.sqrt 3 := by
      have h7 : Complex.abs (z ^ 3 - 3 * z - 2) = Real.sqrt ((z ^ 3 - 3 * z - 2).re ^ 2 + (z ^ 3 - 3 * z - 2).im ^ 2) := by
        simp [Complex.abs, Complex.normSq]
        <;> ring_nf
      rw [h7]
      have h10 : (z ^ 3 - 3 * z - 2).re ^ 2 + (z ^ 3 - 3 * z - 2).im ^ 2 ≤ (3 * Real.sqrt 3) ^ 2 := by
        simp [pow_two, pow_three, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_add, add_mul]
        nlinarith [sq_nonneg (z.re ^ 2 - 3 / 4), sq_nonneg (z.im ^ 2 - 3 / 4), sq_nonneg (z.re * z.im), Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by linarith), sq_nonneg (z.re - 1 / 2), sq_nonneg (z.im - Real.sqrt 3 / 2), sq_nonneg (z.re + 1 / 2), sq_nonneg (z.im + Real.sqrt 3 / 2), sq_nonneg (z.re ^ 2 - z.im ^ 2), sq_nonneg (2 * z.re * z.im)]
      have h9 : Real.sqrt ((z ^ 3 - 3 * z - 2).re ^ 2 + (z ^ 3 - 3 * z - 2).im ^ 2) ≤ Real.sqrt ((3 * Real.sqrt 3) ^ 2) := Real.sqrt_le_sqrt (by linarith [h10])
      have h5 : Real.sqrt ((3 * Real.sqrt 3) ^ 2) = 3 * Real.sqrt 3 := by
        rw [Real.sqrt_sq (by positivity)]
      linarith [h5, h9]
    linarith [h4]