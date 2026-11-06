import Mathlib

theorem algebra_18962 {C D : ℤ} (h : ∀ x : ℝ, x ≠ 3 ∧ x ≠ -8 → C / (x - 3) + D / (x + 8) = (4 * x - 23) / (x ^ 2 + 5 * x - 24)) :
    C * D = -5 := by 
  have eq1 := h 4 ⟨by norm_num, by norm_num⟩
  have eq2 := h (-4) ⟨by norm_num, by norm_num⟩
  
  have eq3 : (C : ℝ) + (D : ℝ) / 12 = -7 / 12 := by
    norm_num at eq1 
    field_simp at eq1 ⊢
    linarith
  
  have eq4 : (C : ℝ) / (-7) + (D : ℝ) / 4 = 39 / 28 := by 
    norm_num at eq2 
    field_simp at eq2 ⊢
    linarith
  
  have eq5 : (12 * (C : ℝ) + (D : ℝ)) = -7 := by
    have eq5 : 12 * (C : ℝ) + (D : ℝ) = -7 := by
      field_simp at eq3 ⊢
      linarith
    linarith
  
  have eq6 : (-4 * (C : ℝ) + 7 * (D : ℝ)) = 39 := by
    have eq6 : -4 * (C : ℝ) + 7 * (D : ℝ) = 39 := by
      field_simp at eq4 ⊢
      linarith
    linarith
  
  have eq7 : (C : ℝ) = (-1 : ℝ) := by
    have eqC : (C : ℝ) = (-1 : ℝ) := by
      linarith [eq5, eq6]
    exact eqC
  
  have hC : C = -1 := by
    exact_mod_cast eq7
  
  have eq8 : (D : ℝ) = (5 : ℝ) := by
    rw [eq7] at eq5
    linarith
  
  have hD : D = 5 := by
    exact_mod_cast eq8
  
  rw [hC, hD]
  all_goals norm_num