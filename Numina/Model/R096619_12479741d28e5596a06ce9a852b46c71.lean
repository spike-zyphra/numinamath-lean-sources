import Mathlib

theorem algebra_274593 (u : ℝ) (x : ℝ) (h₀ : u = -6) (h₁ : x = (3 - 4 * u) / 3) :
    x = 9 := by
  rw [h₁]
  rw [h₀]
  norm_num