import Mathlib

theorem algebra_283632 (x y z : ℤ) (h₀ : x = 5) (h₁ : y = x + 3) (h₂ : z = 3 * y + 1) :
    z = 25 := by
  rw [h₀] at h₁
  have hy : y = 8 := by 
    linarith
  rw [hy] at h₂
  linarith