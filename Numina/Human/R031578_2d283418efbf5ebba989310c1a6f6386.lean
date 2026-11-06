import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_185588 (r : ℝ) (hr : r > 0) (k : ℝ) :
    ∫ x in (0)..r, 4 * π * x * k * x ^ 2 = k * π * r ^ 4 := by
  simp [intervalIntegral.integral_const, mul_assoc, mul_comm, mul_left_comm, add_right_comm]
  ring
  <;> simp [pow_succ, mul_assoc]
  <;> ring_nf <;> simp [hr]
  <;> ring