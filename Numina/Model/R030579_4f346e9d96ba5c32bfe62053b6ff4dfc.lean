import Mathlib

theorem algebra_96854 (x y : ℤ) (h₀ : x * 2 + y * 3 = 100) (h₁ : y = 28) :
x = 8 := by
  rw [h₁] at h₀
  have h2 : x * 2 = 16 := by
    linarith
  have h3 : x = 8 := by
    linarith
  exact h3