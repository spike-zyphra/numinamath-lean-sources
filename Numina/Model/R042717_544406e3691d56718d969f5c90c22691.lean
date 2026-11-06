import Mathlib

open Real


theorem algebra_18908 {S : ℝ → ℝ} (d1 d2 : ℝ) (h1 : d1 = 12) (h2 : d2 = 16) (hS : ∀d, S d = (d / 2)^2 * π) : (3/8) * S d2 - (3/8) * S d1 = 21 * Real.pi / 2 := by
  rw [h1, h2]
  have hS12 : S 12 = (12 / 2)^2 * Real.pi := hS 12
  have hS16 : S 16 = (16 / 2)^2 * Real.pi := hS 16
  rw [hS16, hS12]
  ring_nf