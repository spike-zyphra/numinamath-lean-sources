import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_155288 : ¬ DifferentiableAt ℝ tan (π/2) := by
  rw [Real.differentiableAt_tan]
  simp [Real.cos_pi_div_two]