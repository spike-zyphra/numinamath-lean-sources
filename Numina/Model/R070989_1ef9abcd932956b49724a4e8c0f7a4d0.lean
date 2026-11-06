import Mathlib

theorem algebra_17006 (h m : ℝ) (h₀ : h = 7) (h₁ : m = 0) :
    min (360 * h / 12 - 360 * m / 60) (360 - (360 * h / 12 - 360 * m / 60)) = 150 := by
  rw [h₀, h₁]
  norm_num [min_eq_right]