import Mathlib

open Real Set
open scoped Real

theorem calculus_298513 (f : ℝ → ℝ) (hf : f = sin) :
    deriv (λ x => f (x / 180 * π)) = λ x => π / 180 * cos (x / 180 * π) := by
  rw [hf]
  funext x
  simp [Real.deriv_sin, mul_comm]
  all_goals field_simp [Real.deriv_sin, mul_comm]
  all_goals ring