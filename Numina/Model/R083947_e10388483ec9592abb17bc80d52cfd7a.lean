import Mathlib

theorem algebra_7995 {x y : ℤ} (h₀ : x + y = 9) (h₁ : x * y = -7) :
    x * y - x - y = -16 := by 
  have h2 : x * y - (x + y) = -16 := by 
    rw [h₀, h₁]
    norm_num 
  linarith