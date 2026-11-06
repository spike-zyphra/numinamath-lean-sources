import Mathlib

open Complex ComplexConjugate

theorem algebra_15454 {z : ℂ} : 2 * z - 3 * I * conj z = - 7 + 3 * I ↔ z = 1 + 3 * I := by
  constructor
  · -- Assume 2z - 3i * conjugate(z) = -7 + 3i, prove z = 1 + 3i
    intro h
    have eq1 := congr_arg Complex.re h
    have eq2 := congr_arg Complex.im h
    have h1 : z.re = 1 := by
      simp [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.I_re, Complex.I_im, sub_eq_zero] at eq1 eq2
      nlinarith 
    have h2 : z.im = 3 := by
      simp [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.I_re, Complex.I_im, sub_eq_zero] at eq1 eq2
      nlinarith 
    rw [Complex.ext_iff] at *
    simp [h1, h2]
  · -- Assume z = 1 + 3i, prove 2z - 3i * conjugate(z) = -7 + 3i
    intro h
    rw [h]
    simp [Complex.ext_iff, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    all_goals norm_num