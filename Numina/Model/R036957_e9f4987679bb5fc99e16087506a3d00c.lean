import Mathlib

open Complex Polynomial

theorem algebra_98111 {a b c d : ℝ} (f : ℂ → ℂ) (hf : ∀ x, f x = x ^ 4 + a * x ^ 3 + b * x ^ 2 + c * x + d)
    (h1 : f (2 * I) = 0) (h2 : f (2 + I) = 0) :
    a + b + c + d = 9 := by
  have h11 := hf (2 * I)
  rw [h11] at h1
  have h12 := hf (2 + I)
  rw [h12] at h2
  have eq1 := congr_arg Complex.re h1
  have eq2 := congr_arg Complex.im h1
  have eq3 := congr_arg Complex.re h2
  have eq4 := congr_arg Complex.im h2
  simp [pow_two, pow_three, pow_succ, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.I_re, Complex.I_im, mul_add, mul_assoc] at eq1 eq2 eq3 eq4
  ring_nf at eq1 eq2 eq3 eq4
  linarith