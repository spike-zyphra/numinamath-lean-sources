import Mathlib

theorem algebra_187920 {a b c : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (h1 : a * b = 3 * (a + b)) (h2 : b * c = 4 * (b + c)) (h3 : a * c = 5 * (a + c)) :
    a = 120 / 17 ∧ b = 120 / 23 ∧ c = 120 / 7 := by

  have eq1 : 1 / a + 1 / b = 1 / 3 := by
    field_simp [ha, hb] at h1 ⊢
    linarith

  have eq2 : 1 / b + 1 / c = 1 / 4 := by 
    field_simp [hb, hc] at h2 ⊢
    linarith
  
  have eq3 : 1 / a + 1 / c = 1 / 5 := by 
    field_simp [ha, hc] at h3 ⊢ 
    linarith
  
  have eq4 : 1 / a + 1 / b + 1 / c = 47 / 120 := by 
    linarith [eq1, eq2, eq3]

  have ha1 : 1 / a = 17 / 120 := by 
    have h5 : 1 / a = (47 / 120) - (1 / b + 1 / c) := by
      linarith [eq4]
    rw [h5] 
    linarith [eq2]

  have hb1 : 1 / b = 23 / 120 := by 
    have h6 : 1 / b = (47 / 120) - (1 / a + 1 / c) := by
      linarith [eq4]
    rw [h6]
    linarith [eq3]

  have hc1 : 1 / c = 7 / 120 := by 
    have h7 : 1 / c = (47 / 120) - (1 / a + 1 / b) := by
      linarith [eq4]
    rw [h7] 
    linarith [eq1]

  have ha2 : a = 120 / 17 := by 
    have h8 : a ≠ 0 := ha 
    field_simp [ha, h8] at ha1 ⊢ 
    linarith
  
  have hb2 : b = 120 / 23 := by 
    have h9 : b ≠ 0 := hb 
    field_simp [hb, h9] at hb1 ⊢ 
    linarith
  
  have hc2 : c = 120 / 7 := by 
    have h10 : c ≠ 0 := hc 
    field_simp [hc, h10] at hc1 ⊢ 
    linarith
  
  exact ⟨ha2, hb2, hc2⟩