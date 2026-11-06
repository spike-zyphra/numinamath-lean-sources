import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_156753 : ∫ x in (1)..2, (1 / x) = log 2 := by
  norm_num
  <;> try { simp [intervalIntegral.integral_const, log_one] }
  <;> try { linarith }