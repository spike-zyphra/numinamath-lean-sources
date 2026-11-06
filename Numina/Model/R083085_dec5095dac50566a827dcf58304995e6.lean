import Mathlib

theorem algebra_31 (total_cars : ℕ) (total_hours : ℕ) (h₀ : total_cars = 1440) (h₁ : total_hours = 24) :
    total_cars / (total_hours * 60) = 1 := by 
  calc
    total_cars / (total_hours * 60) = 1440 / (24 * 60) := by 
      rw [h₀, h₁]
    _ = 1440 / 1440 := by 
      norm_num
    _ = 1 := by 
      norm_num