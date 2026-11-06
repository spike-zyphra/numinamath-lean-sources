import Mathlib

theorem algebra_306162 {x : ℂ} (hx : x ≠ 0) (h : x + 1/x = 1) :
    x^2014 + 1/x^2014 = -1 := by 
  have h2 : x ^ 2 + 1 = x := by 
    have h3 : x + 1 / x = 1 := h 
    have eq1 : x + 1 / x = 1 := h3 
    have eq2 : (x + 1 / x) * x = 1 * x := by 
      rw [eq1]
    have eq3 : (x + 1 / x) * x = x ^ 2 + 1 := by 
      field_simp [hx] 
      <;> ring 
    have eq4 : 1 * x = x := by 
      ring 
    rw [eq3, eq4] at eq2 
    exact_mod_cast eq2
  have h3 : x ^ 2 + 1 / x ^ 2 = -1 := by
    have eq1 : x + 1 / x = 1 := h
    have eq2 : (x + 1 / x) ^ 2 = 1 := by 
      rw [eq1]
      all_goals norm_num 
    have eq3 : (x + 1 / x) ^ 2 = x ^ 2 + 1 / x ^ 2 + 2 := by 
      field_simp [hx] 
      <;> ring 
    rw [eq3] at eq2 
    have eq4 : x ^ 2 + 1 / x ^ 2 = -1 := by
      have eq5 : x ^ 2 + 1 / x ^ 2 = (x ^ 2 + 1 / x ^ 2 + 2) - 2 := by ring 
      rw [eq5, eq2]
      all_goals norm_num 
    exact_mod_cast eq4 
  have h4 : x ^ 4 + 1 / x ^ 4 = -1 := by 
    have eq1 : x ^ 2 + 1 / x ^ 2 = -1 := h3
    have eq2 : (x ^ 2 + 1 / x ^ 2) ^ 2 = 1 := by 
      rw [eq1]
      all_goals norm_num 
    have eq3 : (x ^ 2 + 1 / x ^ 2) ^ 2 = x ^ 4 + 1 / x ^ 4 + 2 := by 
      field_simp [hx]
      <;> ring 
    rw [eq3] at eq2 
    have eq5 : x ^ 4 + 1 / x ^ 4 = -1 := by 
      have eq5 : x ^ 4 + 1 / x ^ 4 = (x ^ 4 + 1 / x ^ 4 + 2) - 2 := by ring 
      rw [eq5, eq2]
      all_goals norm_num 
    exact_mod_cast eq5 
  have h5 : x ^ 3 = -1 := by 
    have h6 : x ^ 2 + 1 = x := h2 
    have h7 : x ^ 2 = x - 1 := by 
      calc 
        x ^ 2 = x ^ 2 + 1 - 1 := by ring 
        _ = x - 1 := by rw [h6]; all_goals ring 
    have h8 : x ^ 3 = -1 := by
      calc 
        x ^ 3 = x * x ^ 2 := by ring 
        _ = x * (x - 1) := by rw [h7] 
        _ = (x ^ 2 - x) := by ring 
        _ = -1 := by 
          have h9 : x ^ 2 - x = -1 := by 
            have h6' : x ^ 2 + 1 = x := h6 
            calc 
              x ^ 2 - x = (x ^ 2 + 1) - x - 1 := by ring 
              _ = x - x - 1 := by rw [h6']
              _ = -1 := by ring 
          rw [h9] 
    exact_mod_cast h8 
  have h8 : x ^ 6 = 1 := by 
    have h3 : x ^ 3 = -1 := h5 
    calc 
      x ^ 6 = (x ^ 3) ^ 2 := by ring 
      _ = (-1) ^ 2 := by rw [h3]
      _ = 1 := by norm_num 
  have h9 : x ^ 2014 = x ^ 4 := by 
    calc 
      x ^ 2014 = x ^ ( 6 * 335 + 4 ) := by norm_num 
      _ = (x ^ 6 ) ^ 335 * x ^ 4 := by ring 
      _ = (1) ^ 335 * x ^ 4 := by rw [h8]
      _ = 1 * x ^ 4 := by ring 
      _ = x ^ 4 := by ring 
  have h10 : 1 / x ^ 2014 = 1 / x ^ 4 := by 
    rw [show x ^ 2014 = x ^ 4 by exact_mod_cast h9]
  rw [h10, h9] 
  exact h4