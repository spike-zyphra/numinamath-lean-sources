import Mathlib

theorem calculus_22030 (x y : ℝ → ℝ) (hx : x = fun t => 2 * t + 5) (hy : y = fun t => 12 * t ^ 2 - 8 * t - 7) : ∀ t, y t = 3 * (x t) ^ 2 + (-34) * (x t) + 88 := by
  intro t
  rw [hy, hx]
  ring