import Mathlib

theorem calculus_144177 : ∫ x in (2)..7, (x - 3)^2 = 65 / 3 := by
  norm_num [intervalIntegral.integral_const, mul_comm, mul_assoc]
  <;> ring_nf <;> norm_num