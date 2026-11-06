import Mathlib

theorem algebra_11495 {x y z w : ℝ} (h₀ : x = y + 5) (h₁ : y = z + 10) (h₂ : z = w + 20)
    (h₃ : w = 80) : x = 115 := by 
  rw [h₀, h₁, h₂, h₃]
  norm_num