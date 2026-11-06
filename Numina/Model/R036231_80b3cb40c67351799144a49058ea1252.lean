import Mathlib

theorem algebra_513 {x : ℂ} (hx : x^4 ≠ 0) (h : 23 = x ^ 4 + 1 / x ^ 4) : x ^ 2 + 1 / x ^ 2 = 5 ∨ x ^ 2 + 1 / x ^ 2 = -5 := by
  have h1 : x ^ 4 + 1 / x ^ 4 = 23 := by 
    have h1 : 23 = x ^ 4 + 1 / x ^ 4 := h 
    rw [eq_comm] at h1 
    exact h1 
  have h2 : (x ^ 2 + 1 / x ^ 2) ^ 2 = 25 := by 
    have eq3 : (x ^ 2 + 1 / x ^ 2) ^ 2 = x ^ 4 + 1 / x ^ 4 + 2 := by
      have h5 : x ≠ 0 := by 
        by_contra h6 
        have : x^4 = 0 := by 
          calc 
            x^4 = (x)^4 := by ring 
            _ = (0)^4 := by rw [h6] 
            _ = 0 := by norm_num 
        contradiction
      have eq4 : (x ^ 2 + 1 / x ^ 2) ^ 2 = x^4 + 2 + 1/x^4 := by
        have hne : x ≠ 0 := h5 
        field_simp [hne]
        <;> ring 
      have eq5 : x ^ 4 + 2 + 1 / x ^ 4 = x ^ 4 + 1 / x ^ 4 + 2 := by ring 
      rw [eq4, eq5]
    have eq4 : x ^ 4 + 1 / x ^ 4 = 23 := h1 
    rw [eq3, eq4] 
    all_goals norm_num 
  have h3 : (x ^ 2 + 1 / x ^ 2 - 5) * (x ^ 2 + 1 / x ^ 2 + 5) = 0 := by
    have h4 : (x ^ 2 + 1 / x ^ 2) ^ 2 = 25 := h2 
    have h5 : (x ^ 2 + 1 / x ^ 2) ^ 2 - 25 = 0 := by 
      rw [h4] 
      norm_num 
    calc 
      (x ^ 2 + 1 / x ^ 2 - 5) * (x ^ 2 + 1 / x ^ 2 + 5) = (x ^ 2 + 1 / x ^ 2) ^ 2 - 25 := by 
        ring 
      _ = 0 := h5 
  cases' (mul_eq_zero.1 h3) with h4 h5 
  · -- Case h4 : (x ^ 2 + 1 / x ^ 2 - 5) = 0 
    have h6 : x ^ 2 + 1 / x ^ 2 = 5 := by 
      have h7 : x ^ 2 + 1 / x ^ 2 - 5 = 0 := h4 
      calc 
        x ^ 2 + 1 / x ^ 2 = (x ^ 2 + 1 / x ^ 2 - 5) + 5 := by ring 
        _ = (0) + 5 := by rw [h7] 
        _ = (5 : ℂ) := by ring 
    left 
    exact h6 
  · -- Case h5 : (x ^ 2 + 1 / x ^ 2 + 5) = 0 
    have h8 : x ^ 2 + 1 / x ^ 2 = -5 := by 
      have h9 : x ^ 2 + 1 / x ^ 2 + 5 = 0 := h5 
      calc 
        x ^ 2 + 1 / x ^ 2 = (x ^ 2 + 1 / x ^ 2 + 5) - 5 := by ring 
        _ = (0) - 5 := by rw [h9] 
        _ = (-5 : ℂ) := by ring
    right
    exact h8