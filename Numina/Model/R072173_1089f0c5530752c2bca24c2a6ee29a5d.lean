import Mathlib

theorem algebra_14540 {a b : ℝ} (ha : (a + 4 * Complex.I)^2 - (10 + 9 * Complex.I) * (a + 4 * Complex.I) + (4 + 46 * Complex.I) = 0)
    (hb : (b + 5 * Complex.I)^2 - (10 + 9 * Complex.I) * (b + 5 * Complex.I) + (4 + 46 * Complex.I) = 0) :
    a = 6 ∧ b = 4 := by
  have eq1 := ha
  have eq2 := hb
  have h_eq_a : a = 6 := by
    have h1 := congr_arg Complex.re eq1
    have h2 := congr_arg Complex.im eq1
    simp [pow_two, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im] at h1 h2
    nlinarith [sq_nonneg (a - 6), sq_nonneg (a - 4)]
  have h_eq_b : b = 4 := by
    have h1 := congr_arg Complex.re eq2
    have h2 := congr_arg Complex.im eq2
    simp [pow_two, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im] at h1 h2
    nlinarith [sq_nonneg (b - 4), sq_nonneg (b - 6)]
  exact ⟨h_eq_a, h_eq_b⟩