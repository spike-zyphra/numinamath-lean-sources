import Mathlib

theorem algebra_299158 {x y z : ℝ} (h₀ : x * y / (x + 2 * y) = 1) (h₁ : y * z / (y + 2 * z) = 2) (h₂ : z * x / (z + 2 * x) = 3) :
    10 * x + 7 * y + z = 0 := by
  have h3 : x + 2 * y ≠ 0 := by 
    by_contra h
    have eq1 : x * y / (x + 2 * y) = 0 := by 
      rw [h]
      norm_num
    linarith
  have h4 : y + 2 * z ≠ 0 := by
    by_contra h
    have eq1 : y * z / (y + 2 * z) = 0 := by 
      rw [h]
      norm_num
    linarith
  have h5 : z + 2 * x ≠ 0 := by
    by_contra h
    have eq1 : z * x / (z + 2 * x) = 0 := by 
      rw [h]
      norm_num
    linarith
  have eq1 : x * y = x + 2 * y := by 
    have h6 : x * y / (x + 2 * y) = 1 := h₀ 
    field_simp [h3] at h6 
    linarith 
  have eq2 : y * z = 2 * (y + 2 * z) := by 
    have h7 : y * z / (y + 2 * z) = 2 := h₁ 
    field_simp [h4] at h7 
    linarith 
  have eq3 : z * x = 3 * (z + 2 * x) := by
    have h8 : z * x / (z + 2 * x) = 3 := h₂
    field_simp [h5] at h8 
    linarith
  nlinarith [sq_nonneg (x - 27 / 10), sq_nonneg (y - 27 / 7), sq_nonneg (z + 54), sq_pos_of_ne_zero (show (x + 2 * y) ≠ 0 by assumption), sq_pos_of_ne_zero (show (y + 2 * z) ≠ 0 by assumption), sq_pos_of_ne_zero (show (z + 2 * x) ≠ 0 by assumption)]