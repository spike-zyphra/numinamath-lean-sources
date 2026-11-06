import Mathlib

open Polynomial

theorem algebra_19434 : (3 * (X - 4) + 2 * (X ^ 2 - X + 7) - 5 * (X - 1) : ℤ[X]).coeff 0 = 7 := by
  ring_nf
  simp [coeff_eq_zero_of_natDegree_lt]
  <;> try { norm_num }
  <;> try { rfl }
  <;> try { omega }