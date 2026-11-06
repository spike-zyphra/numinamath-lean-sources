import Mathlib

theorem algebra_306420 {a b c : ℝ} (h₀ : a * b / (a + b) = 1 / 15) (h₁ : b * c / (b + c) = 1 / 17)
    (h₂ : c * a / (c + a) = 1 / 16) :
    a * b * c / (a * b + b * c + c * a) = 1 / 24 := by

  have h3 : a + b ≠ 0 := by
    by_contra h
    have eq1 : a * b / (a + b) = 0 := by 
      rw [h]
      norm_num 
    linarith
  have h4 : b + c ≠ 0 := by
    by_contra h
    have eq1 : b * c / (b + c) = 0 := by 
      rw [h]
      norm_num 
    linarith
  have h5 : c + a ≠ 0 := by
    by_contra h
    have eq1 : c * a / (c + a) = 0 := by 
      rw [h]
      norm_num 
    linarith
  
  have ha1 : a ≠ 0 := by
    by_contra h
    have h4 : a = 0 := by linarith
    have eq1 : a * b / (a + b) = 0 := by
      rw [h4]
      norm_num
    linarith

  have hb1 : b ≠ 0 := by
    by_contra h
    have h5 : b = 0 := by linarith
    have eq1 : a * b / (a + b) = 0 := by 
      rw [h5]
      norm_num 
    linarith

  have hc1 : c ≠ 0 := by 
    by_contra h
    have h6 : c = 0 := by linarith
    have eq2 : b * c / (b + c) = 0 := by 
      rw [h6]
      norm_num 
    linarith
  
  -- Derive the reciprocals equations 
  have eq1 : 1 / a + 1 / b = 15 := by
    have eq3 : a * b / (a + b) = 1 / 15 := h₀
    have h4 : a + b ≠ 0 := h3
    have eq4 : 15 * (a * b) = a + b := by
      have h6 : a + b ≠ 0 := h4
      field_simp [h6] at eq3 ⊢ 
      nlinarith 
    have eq5 : (a + b) = 15 * (a * b) := by 
      linarith 
    have h6 : a ≠ 0 := ha1
    have h7 : b ≠ 0 := hb1
    field_simp [h6, h7] at eq5 ⊢ 
    nlinarith

  have eq2 : 1 / b + 1 / c = 17 := by 
    have eq4 : b * c / (b + c) = 1 / 17 := h₁ 
    have h5 : b + c ≠ 0 := h4
    have eq5 : 17 * (b * c) = b + c := by 
      have h7 : b + c ≠ 0 := h5
      field_simp [h7] at eq4 ⊢ 
      nlinarith 
    have eq6 : (b + c) = 17 * (b * c) := by 
      linarith 
    have h8 : b ≠ 0 := hb1
    have h9 : c ≠ 0 := hc1
    field_simp [h8, h9] at eq6 ⊢ 
    nlinarith

  have eq3 : 1 / a + 1 / c = 16 := by 
    have eq4 : c * a / (c + a) = 1 / 16 := h₂
    have h6 : c + a ≠ 0 := h5
    have eq5 : 16 * (c * a) = c + a := by 
      have h7 : c + a ≠ 0 := h6
      field_simp [h7] at eq4 ⊢ 
      nlinarith 
    have eq6 : (c + a) = 16 * (c * a) := by 
      linarith 
    have h8 : a ≠ 0 := ha1
    have h9 : c ≠ 0 := hc1
    field_simp [h8, h9] at eq6 ⊢ 
    nlinarith
  
  -- Solve the system
  have h6 : 1 / b = 8 := by 
    linarith [eq1, eq2, eq3]

  have hb : b = 1 / 8 := by 
    have h7 : b ≠ 0 := hb1
    field_simp at h6 ⊢
    linarith

  have h7 : 1 / a = 7 := by 
    linarith [eq1, h6, eq3]

  have ha : a = 1 / 7 := by
    have h8 : a ≠ 0 := ha1
    field_simp at h7 ⊢ 
    linarith

  have h8 : 1 / c = 9 := by 
    linarith [eq3, h7, h6]

  have hc : c = 1 / 9 := by 
    have h9 : c ≠ 0 := hc1
    field_simp at h8 ⊢ 
    linarith
  
  -- Substitute to final expression
  have h8 : a * b * c = 1 / 504 := by 
    rw [ha, hb, hc]
    norm_num 
  have h9 : a * b + b * c + c * a = 24 / 504 := by 
    rw [ha, hb, hc]
    norm_num 
  rw [h8, h9] 
  norm_num 
  all_goals norm_num