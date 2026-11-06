import Mathlib

theorem algebra_268882 {r b : ℕ} (h₀ : r = b + 6) (h₁ : r * 3 = b * 5) :
    r + b = 24 := by
  rw [h₀] at h₁
  have hb : b = 9 := by 
    omega 
  have hr : r = 15 := by 
    omega 
  calc 
    r + b = 15 + 9 := by rw [hr, hb]
    _ = 24 := by norm_num