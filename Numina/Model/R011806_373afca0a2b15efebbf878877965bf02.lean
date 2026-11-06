import  Mathlib

theorem algebra_609739  (A B C D : ℝ) (h₀ : A < B ∧ B < C ∧ C < D)  (h₁ : (B - A) / (C - B) = (D - A) / (D - C)) (h₂ : C - A = 3) (h₃ : D - B = 4) : D - A = 6 := by
  rcases h₀ with ⟨h4, h5, h6⟩
  have h7 : C = A + 3 := by linarith 
  have h8 : D = B + 4 := by linarith
  have eq1 : D - C = (B - A) + 1 := by 
    rw [show C = A + 3 by linarith [h7]] 
    rw [show D = B + 4 by linarith [h8]] 
    linarith
  have eq2 : C - B = 3 - (B - A) := by
    rw [show C = A + 3 by linarith [h7]] 
    linarith
  have eq3 : (B - A) * (D - C) = (C - B) * (D - A) := by 
    have h9 : C - B ≠ 0 := by
      linarith
    have h10 : D - C ≠ 0 := by
      linarith
    field_simp [h9, h10] at h₁
    linarith
  have eq4 : D - A = (B - A) + 4 := by 
    linarith [h₃]
  rw [show D - C = (B - A) + 1 by linarith [eq1]] at eq3
  rw [show C - B = 3 - (B - A) by linarith [eq2]] at eq3
  rw [eq4] at eq3
  have hx1 : (B - A) = 2 := by
    nlinarith [sq_nonneg (B - A - 2), sq_nonneg (B - A + 3), mul_pos (sub_pos.mpr h4) (sub_pos.mpr h5), mul_pos (sub_pos.mpr h5) (sub_pos.mpr h6)]
  linarith [hx1, h₃]