import Mathlib

open Complex
open ComplexConjugate

theorem algebra_21158 {a b : ℂ}
    (hab : a * conj b = -1 + 5 * I) :
    conj a * b = -1 - 5 * I := by
  rw [show conj a * b = conj (a * conj b) by simp, hab]
  simp [conj_eq_iff_re.mpr]
  ring_nf
