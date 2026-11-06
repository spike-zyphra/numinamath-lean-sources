import Mathlib

theorem algebra_13456 (a b : ℝ) (h : (1 - 2 * Complex.I)^3 + a * (1 - 2 * Complex.I)^2 - (1 - 2 * Complex.I) + b = 0) :
    a = 1 ∧ b = 15 := by 
  have eq1 := congr_arg Complex.re h
  have eq2 := congr_arg Complex.im h
  simp [pow_two, pow_three, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, 
        Complex.I_re, Complex.I_im] at eq1 eq2
  ring_nf at eq1 eq2
  constructor 
  · -- First solve for a
    linarith 
  · -- Now solve for b using a = 1 
    linarith