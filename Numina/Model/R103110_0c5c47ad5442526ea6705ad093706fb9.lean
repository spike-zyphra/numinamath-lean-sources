import Mathlib

theorem algebra_19666 (h m : ℝ) (h₀ : h = 8) (h₁ : m = 0) :
    min (360 * h / 12 - 360 * m / 60) (360 - 360 * h / 12 + 360 * m / 60) = 120 := by
  rw [h₀, h₁]
  norm_num