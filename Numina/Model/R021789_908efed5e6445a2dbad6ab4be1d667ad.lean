import Mathlib

theorem calculus_144136 : ∫ x in (0)..2, (x - 1)^3 = 0 := by 
  -- We need to prove ∫ (x : ℝ) in 0 ..2, (x - 1)^3 = 0.
  norm_num [intervalIntegral.integral_const, add_mul, mul_add, mul_assoc]
  <;> ring_nf <;> norm_num
  <;> ring_nf <;> norm_num
  <;> linarith
  <;> ring_nf <;> norm_num
  <;> ring_nf <;> norm_num
  <;> ring_nf <;> norm_num