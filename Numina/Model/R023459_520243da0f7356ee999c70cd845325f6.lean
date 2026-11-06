import Mathlib

theorem algebra_11808 (total_faces : ℕ) (h₀ : total_faces = 8)
    (yellow_faces : ℕ) (h₁ : yellow_faces = 3) :
    (yellow_faces : ℝ) / total_faces = 3 / 8 := by 
  rw [h₀, h₁]
  all_goals norm_num