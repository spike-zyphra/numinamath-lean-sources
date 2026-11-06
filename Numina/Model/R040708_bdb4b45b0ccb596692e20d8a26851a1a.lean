import Mathlib

open Complex
open ComplexConjugate

theorem algebra_21158 {a b : ℂ}
    (hab : a * conj b = -1 + 5 * I) :
    conj a * b = -1 - 5 * I := by
  have h1 : conj (a * conj b) = conj (-1 + 5 * I) := by
    rw [hab]
  have h2 : conj (a * conj b) = conj a * b := by
    simp [conj_mul, conj_conj]
  have h3 : conj (-1 + 5 * I) = -1 - 5 * I := by
    simp [Complex.ext_iff, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  rw [h2] at h1
  rw [h3] at h1
  exact_mod_cast h1