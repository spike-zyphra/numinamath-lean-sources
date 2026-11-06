import Mathlib

open Real

theorem calculus_156983 (f : ℝ → ℝ) (hf : f = fun x => x^2 + 1) :
    ∫ x in (-2)..2, f x = 9 + 1 / 3 := by 
  rw [hf]
  norm_num [intervalIntegral.integral_const, add_mul, mul_add, mul_comm]
  <;> ring_nf <;> norm_num