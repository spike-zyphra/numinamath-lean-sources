import Mathlib

theorem algebra_270517 (a r : ℤ) (h₀ : a = 2) (h₁ : r = 3) :
    a * r^4 = 162 := by 
  rw [h₀, h₁]
  norm_num