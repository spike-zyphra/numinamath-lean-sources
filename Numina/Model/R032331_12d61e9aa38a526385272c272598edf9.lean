import Mathlib

theorem algebra_1658 {x : ℝ} (hx : x ≠ 0) (h : x + 1/x = 1) :
    x^7 + 1/x^7 = 1 := by

  have h2 : x^2 + 1/x^2 = -1 := by
    have eq1 : x + 1/x = 1 := h
    calc
      x^2 + 1/x^2 = (x + 1/x) ^ 2 - 2 := by 
          field_simp
          ring
      _ = (1) ^ 2 - 2 := by rw [eq1]
      _ = -1 := by norm_num

  have h3 : x^3 + 1/x^3 = -2 := by 
    have eq1 : x + 1/x = 1 := h 
    have eq2 : x^2 + 1/x^2 = -1 := h2 
    calc 
      x^3 + 1/x^3 = (x + 1/x) * (x^2 + 1/x^2) - (x + 1/x) := by 
        field_simp 
        ring 
      _ = (1) * (-1) - (1) := by rw [eq1, eq2] 
      _ = -2 := by norm_num

  have h4 : x^4 + 1/x^4 = -1 := by 
    have eq2 : x^2 + 1/x^2 = -1 := h2 
    calc 
      x^4 + 1/x^4 = (x^2 + 1/x^2) ^ 2 - 2 := by 
          field_simp 
          ring 
      _ = (-1) ^ 2 - 2 := by rw [eq2]
      _ = -1 := by norm_num

  have h5 : x^5 + 1/x^5 = 1 := by 
    have eq1 : x + 1/x = 1 := h 
    have eq4 : x^4 + 1/x^4 = -1 := h4 
    have eq3 : x^3 + 1/x^3 = -2 := h3 
    calc 
      x^5 + 1/x^5 = (x + 1/x) * (x^4 + 1/x^4) - (x^3 + 1/x^3) := by 
        field_simp 
        ring 
      _ = (1) * (-1) - (-2) := by rw [eq1, eq4, eq3] 
      _ = 1 := by norm_num

  have h6 : x^6 + 1/x^6 = 2 := by 
    have eq3 : x^3 + 1/x^3 = -2 := h3 
    calc 
      x^6 + 1/x^6 = (x^3 + 1/x^3) ^ 2 - 2 := by 
          field_simp 
          ring 
      _ = (-2) ^ 2 - 2 := by rw [eq3] 
      _ = 2 := by norm_num

  have eq1 : x + 1/x = 1 := h 
  have eq6 : x^6 + 1/x^6 = 2 := h6 
  calc 
    x^7 + 1/x^7 = (x + 1/x) * (x^6 + 1/x^6) - (x^5 + 1/x^5) := by 
        field_simp 
        ring 
    _ = (1) * (2) - (1) := by rw [eq1, eq6, h5] 
    _ = 1 := by norm_num