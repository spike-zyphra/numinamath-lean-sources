import Mathlib

theorem algebra_175336 {x y : ℕ} (h₀ : y = x + 480) (h₁ : y + 50 = 5 * (x - 50)) :
    x + y = 870 := by
  rw [h₀] at h₁
  omega