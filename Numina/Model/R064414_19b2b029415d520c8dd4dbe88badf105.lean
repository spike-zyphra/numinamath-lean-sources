import Mathlib

theorem algebra_274473 (x y z : ℝ) (h₀ : x + y + z = 50) (h₁ : x / (y + z) = 3 / 2)
    (h₂ : y = z + 4) : z = 8 := by 
  have h4 : y + z ≠ 0 := by
    by_contra h
    have h5 : y + z = 0 := by linarith
    have h6 : x / (y + z) = 0 := by
      rw [h5]
      norm_num
      all_goals linarith [h₀]
    linarith [h₁, h6]
  have h5 : 2 * x = 3 * (y + z) := by
    have h : y + z ≠ 0 := h4
    field_simp [h] at h₁
    linarith

  rw [show y = z + 4 by linarith [h₂]] at h₀
  have eq1 : x + (z + 4) + z = 50 := by linarith
  have eq2 : x + 2 * z = 46 := by linarith [eq1]
  
  have eq3 : x = 46 - 2 * z := by linarith [eq2]

  rw [show y + z = (z + 4) + z by linarith [h₂]] at h5
  rw [eq3] at h5

  linarith