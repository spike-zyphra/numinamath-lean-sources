import Mathlib

theorem algebra_130625 (j z : ℕ) (h₀ : j < 100) (h₁ : z < 100)
    (h₂ : j = 10 * (z % 10) + (z / 10)) (h₃ : j + 5 = 2 * (z + 5)) :
    j - z = 18 := by 
  interval_cases z <;> norm_num [h₂] at h₃ <;> omega