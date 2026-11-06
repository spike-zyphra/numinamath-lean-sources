import Mathlib

theorem algebra_117170 (m : ℂ) (h : ∃ x : ℝ, (1 + 2 * .I : ℂ) * x ^ 2 + m * x + 1 - 2 * .I = 0) :
    Complex.abs m ≥ 2 := by
  rcases h with ⟨x, hx⟩
  have eq1 := congr_arg Complex.re hx
  have eq2 := congr_arg Complex.im hx
  simp [pow_two, Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im] at eq1 eq2
  have h1 : (x) ^ 2 + m.re * x + 1 = 0 := by
    linarith
  have h2 : 2 * (x) ^ 2 + m.im * x - 2 = 0 := by
    linarith
  have h3 : (m.im) ^ 2 - 4 * (m.re) ^ 2 + 16 = 0 := by
    nlinarith [sq_nonneg (x * 1 - x * 2 * m.re + x * m.im), sq_nonneg (x * m.re - x * m.im), sq_nonneg (x * 2 - m.re * 1), sq_nonneg (x * 1 - m.im * 1 / 2), sq_nonneg (m.re - 2), sq_nonneg (m.re + 2), sq_nonneg (m.re * 2 - m.im), sq_nonneg (m.re ^ 2 - 4), sq_nonneg (m.re * 2 - m.im / 2), sq_nonneg (m.re * 2 - m.im), sq_nonneg (m.re ^ 2 - m.im ^ 2)]
  have h4 : Complex.abs m ≥ 2 := by
    have h5 : Complex.abs m = Real.sqrt (m.re ^ 2 + m.im ^ 2) := by
      simp [Complex.abs, Complex.normSq]
      <;> ring_nf
      <;> simp [Complex.I_sq]
      <;> ring_nf
    rw [h5]
    have h6 : m.re ^ 2 + m.im ^ 2 ≥ 4 := by
      nlinarith [sq_nonneg (m.re * 2 - m.im), sq_nonneg (m.re ^ 2 - 4), sq_nonneg (m.re - 2), sq_nonneg (m.re + 2), sq_nonneg (m.re * 2 - m.im), sq_nonneg (m.re ^ 2 - 4), sq_nonneg (m.re), sq_nonneg (m.im), sq_nonneg (m.re * 2 - m.im / 2), sq_nonneg (m.re * 2 - m.im), sq_nonneg (m.re ^ 2 - 4)]
    have h7 : Real.sqrt (m.re ^ 2 + m.im ^ 2) ≥ Real.sqrt (4 : ℝ) := Real.sqrt_le_sqrt (by linarith)
    have h8 : Real.sqrt (4 : ℝ) = (2 : ℝ) := by
      rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
    linarith [h7, h8]
  exact h4