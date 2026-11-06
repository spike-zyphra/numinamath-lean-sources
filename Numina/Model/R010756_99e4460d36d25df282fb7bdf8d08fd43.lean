import Mathlib

open Polynomial

theorem algebra_15603 {p q: ℤ[X]} (hp: p = -5*X^3-5*X^2-7*X+1)
  (hq: q = -X^2-6*X+1): (p * q).coeff 2 = 36 := by
  rw [hp, hq]
  ring_nf
  <;> norm_num [coeff_eq_zero_of_natDegree_lt]