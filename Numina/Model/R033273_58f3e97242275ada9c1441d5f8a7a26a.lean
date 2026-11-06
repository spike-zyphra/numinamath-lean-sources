import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_151476 (f : ℝ → ℝ) (hf : f = λ x => sin x * (cos x)^2) :
    ∫ x in (0)..(π/2), f x = 1/3 := by 
  rw [hf]
  norm_num [intervalIntegral.integral_const, sin_pi_div_two, cos_pi_div_two, cos_zero]
  <;> ring_nf <;> norm_num [sin_pi_div_two, cos_pi_div_two, cos_zero]