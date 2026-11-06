import Mathlib

theorem algebra_247947 {m : ℝ} (h : ∃! x : ℝ, x^2 + (1 - 2 * Complex.I) * x + 3 * m - Complex.I = 0) :
    (-(1 / 2) + 2 * Complex.I) ^ 2 + (1 - 2 * Complex.I) * (-(1 / 2) + 2 * Complex.I) + 3 * m - Complex.I = 0 := by
  rcases h with ⟨x, h_eq, h1⟩
  have eq1 := congr_arg Complex.re h_eq
  have eq2 := congr_arg Complex.im h_eq 
  simp [pow_two, Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im] at eq1 eq2
  have h2 : x = -1 / 2 := by
    linarith
  have h3 : m = 1 / 12 := by
    rw [show x = -1 / 2 by linarith] at eq1
    nlinarith
  rw [h3]
  simp [pow_two, Complex.ext_iff, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  <;> norm_num <;> ring_nf <;> norm_num
  <;> norm_num
  <;> norm_num