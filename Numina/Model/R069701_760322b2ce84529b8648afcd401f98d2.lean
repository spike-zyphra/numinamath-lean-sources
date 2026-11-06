import Mathlib

theorem algebra_591 (f : ℝ → ℝ) (hf : ∀ x, f x = x + (x / 2) + (x / 4) + (x / 8) + (x / 16) + (x / 32) + (x / 64)) : f 1 = 1 + 63 / 64 := by
  rw [hf]
  norm_num