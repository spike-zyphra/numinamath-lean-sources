import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_5701 :
  ∫ x in (0)..1, π * (x^2)^2 - π * (x^3)^2 = 2 * π / 35 := by
  simp [intervalIntegral.integral_const, mul_comm]
  <;> ring_nf <;> simp [pow_two, pow_succ, mul_add, mul_comm, mul_assoc]
  <;> ring_nf <;> field_simp
  <;> ring_nf <;> field_simp
  <;> ring_nf <;> field_simp
  <;> ring