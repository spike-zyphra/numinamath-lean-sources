import Mathlib

theorem algebra_14081 (total_passengers : ℕ) (h₀ : total_passengers = 200)
    (women_percentage : ℝ) (first_class_percentage : ℝ) (h₁ : women_percentage = 60 / 100)
    (h₂ : first_class_percentage = 10 / 100) :
    (total_passengers * women_percentage) * first_class_percentage = 12 := by
  rw [h₀] at *
  rw [h₁] at *
  rw [h₂] at *
  norm_num