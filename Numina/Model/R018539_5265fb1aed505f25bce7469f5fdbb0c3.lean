import Mathlib

theorem algebra_142906 {a b q r : ℝ} (h : b ≠ 0) (h1 : (a + b * Complex.I)^3 + q * (a + b * Complex.I) + r = 0)
    (h2 : (a - b * Complex.I)^3 + q * (a - b * Complex.I) + r = 0) :
    q = b^2 - 3 * a^2 := by
  have eq1 := congrArg Complex.re h1
  have eq2 := congrArg Complex.im h1
  have eq1' := congrArg Complex.re h2
  have eq2' := congrArg Complex.im h2
  simp [pow_three, Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_add, mul_assoc] at eq1 eq2 eq1' eq2'
  ring_nf at eq1 eq2 eq1' eq2'
  have h3 : b ≠ 0 := h
  have h4 : q = b ^ 2 - 3 * a ^ 2 := by
    apply (mul_left_inj' h3).mp
    nlinarith
  linarith