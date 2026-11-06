import Mathlib
open Real

theorem algebra_3969 (a x : ℝ) (h₁ : 3 * x + 2 * (x - 1) = 2 * (x + 5)) (h₂ : 3 * x - 4 * (a - x) = 6 * x - 5 * (a - x)) : a = 16 := by
  have hx : x = 4 := by
    linarith
  rw [hx] at h₂
  linarith