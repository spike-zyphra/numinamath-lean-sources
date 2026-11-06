import Mathlib

theorem algebra_235380 {a b c : ℝ} (hb : b ≠ 0) (hc : c ≠ 0) (h1 : (a + b) / b = 3 / 2) (h2 : c / (b - c) = 4 / 5) :
    (c - a) / c = -1 / 8 := by
  have eq1 : a = (1 / 2) * b := by 
    have h1' : a + b = (3 / 2) * b := by
      field_simp [hb] at h1 
      linarith 
    linarith
  
  have h3 : b - c ≠ 0 := by
    by_contra h
    have : c / (b - c) = 0 := by 
      rw [h]
      norm_num 
    linarith [h2, this]

  have eq2 : c = (4 / 9) * b := by 
    field_simp [h3] at h2 
    linarith 

  have h4 : c - a = - (1 / 8) * c := by 
    rw [eq1, eq2]
    linarith 
    <;> nlinarith
  
  have h5 : (c - a) / c = -1 / 8 := by 
    have h6 : c - a = - (1 / 8) * c := h4 
    have h7 : c ≠ 0 := hc 
    field_simp [h7] 
    linarith [h6] 

  exact h5