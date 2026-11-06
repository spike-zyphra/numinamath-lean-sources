import Mathlib

open Real Set
open scoped Real

theorem calculus_17122 (θ : ℝ) (h : cos θ = 1 / 4) : cos (3 * θ) = -11 / 16 := by 
  have h1 : cos (3 * θ) = 4 * cos θ ^ 3 - 3 * cos θ := by
    rw [cos_three_mul]
  rw [h1, h]
  norm_num