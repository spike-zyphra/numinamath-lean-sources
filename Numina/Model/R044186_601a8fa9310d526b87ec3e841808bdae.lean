import Mathlib

theorem algebra_20302 {a b : ℂ} (h : a + (b.re - Complex.I * b.im) = 2 - 7 * Complex.I) :
    (a.re - Complex.I * a.im) + b = 2 + 7 * Complex.I := by
  simp [Complex.ext_iff, Complex.add_re, Complex.add_im, Complex.I_re, Complex.I_im, sub_eq_add_neg] at h ⊢
  constructor
  · -- Real part
    linarith
  · -- Imaginary part
    linarith