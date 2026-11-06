import Mathlib

theorem algebra_10946 (a b c d e f : ℝ) (ha : b = 3) (he : e = -a - c)
    (hsum : (a + b * Complex.I) + (c + d * Complex.I) + (e + f * Complex.I) = 2 * Complex.I) :
    d + f = -1 := by

  have eq1 := congr_arg Complex.re hsum
  have eq2 := congr_arg Complex.im hsum

  simp [Complex.add_re, Complex.ofReal_re, Complex.I_re, Complex.add_im, Complex.ofReal_im, Complex.I_im] at eq1 eq2

  rw [ha] at eq2
  rw [he] at eq1
  linarith