import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_144617 : ∫ t in (0)..(2 * π), 4 * 3 / 2 = 12 * π := by 
  simp [intervalIntegral.integral_const]
  <;> ring_nf <;> simp [mul_comm]
  <;> ring