import Mathlib

theorem algebra_278491 {x y : ℤ} (h₀ : x + y = -26) (h₁ : x = 11) : y = -37 := by
  rw [h₁] at h₀
  linarith