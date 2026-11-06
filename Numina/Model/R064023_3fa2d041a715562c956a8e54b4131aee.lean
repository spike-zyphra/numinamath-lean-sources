import Mathlib

theorem algebra_15046 (total_people : ℕ) (h₀ : total_people = 20)
    (left_handed : ℕ) (jzz : ℕ) (zr : ℕ)
    (h₁ : left_handed = 8) (h₂ : jzz = 15) (h₃ : zr = 2) :
    left_handed + jzz - total_people + zr = 5 := by
  calc 
    left_handed + jzz - total_people + zr = 8 + 15 - 20 + 2 := by 
      rw [h₀, h₁, h₂, h₃]
    _ = 5 := by 
      norm_num