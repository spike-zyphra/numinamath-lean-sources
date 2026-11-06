import Mathlib

open Real

theorem calculus_3264 : ∫ x in (2)..11, (1 / (1 - x)) = -log 10 := by
  norm_num [intervalIntegral.integral_const, Finset.sum_range_succ]
  <;> try { native_decide }
  <;> try { field_simp [Real.log_div, Real.log_pow] }
  <;> try { ring_nf }
  <;> try { field_simp [Real.log_div, Real.log_pow] }
  <;> try { ring_nf <;> norm_num }
  <;> try { field_simp [Real.log_div, Real.log_pow] }
  <;> try { ring_nf }
  <;> try { rw [Real.log_one]; norm_num }
  <;> try { linarith }
  <;> try { native_decide }