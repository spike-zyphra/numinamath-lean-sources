import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_177818 {f : ℝ → ℝ} (hf : f = λ x => sin (x^2)) :
    deriv f = λ x => cos (x^2) * 2 * x := by 
  rw [hf]
  funext x
  simp [deriv_pow, differentiableAt_sin, mul_comm]
  <;> ring_nf <;> simp [cos_sq] <;> ring