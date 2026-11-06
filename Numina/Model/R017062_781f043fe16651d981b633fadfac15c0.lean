import Mathlib

theorem algebra_12866 {Z : ℂ} (hZ : (Z - 1)^2 = Complex.abs (Z - 1)^2) :
    Z.im = 0 := by
  have eq1 := congr_arg Complex.re hZ
  have eq2 := congr_arg Complex.im hZ
  simp [pow_two, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.abs, Complex.normSq] at eq1 eq2
  ring_nf at eq1 eq2
  have h1 : Z.im ^ 2 = 0 := by
    nlinarith
  have h2 : Z.im = 0 := by
    nlinarith
  exact h2