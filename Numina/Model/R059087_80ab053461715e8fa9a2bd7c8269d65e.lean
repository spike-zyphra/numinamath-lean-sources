import Mathlib

theorem algebra_326320 {x : ℝ} (hx : x ≠ 0) (h : x - 1/x = 4) :
    x + 1/x = 2*Real.sqrt 5 ∨ x + 1/x = -2*Real.sqrt 5 := by

  have h1 : x ^ 2 + 1 / x ^ 2 = 18 := by 
    have eq1 : x - 1 / x = 4 := h
    have eq2 : x ^ 2 + 1 / x ^ 2 = (x - 1/x) ^ 2 + 2 := by 
      field_simp [hx]
      ring
    rw [eq1] at eq2
    linarith
  
  have h2 : (x + 1 / x) ^ 2 = 20 := by 
    have eq1 : x ^ 2 + 1 / x ^ 2 = 18 := h1 
    have eq2 : (x + 1/x) ^ 2 = x^2 + 1/x^2 + 2 := by 
      field_simp [hx]
      ring 
    rw [eq1] at eq2 
    linarith

  have h3 : x + 1 / x = Real.sqrt 20 ∨ x + 1 / x = -Real.sqrt 20 := by 
    have h4 : (x + 1 / x) ^ 2 = 20 := h2 
    have : (x + 1 / x) ^ 2 - 20 = 0 := by linarith 
    have : (x + 1 / x) ^ 2 - Real.sqrt 20 ^ 2 = 0 := by 
      rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ (20 : ℝ))] 
      linarith 
    have : ((x + 1 / x) - Real.sqrt 20) * ((x + 1 / x) + Real.sqrt 20) = 0 := by 
      linarith [this] 
    cases' (mul_eq_zero.1 this) with h5 h6 
    · left 
      linarith 
    · right 
      linarith 

  have h4 : Real.sqrt 20 = 2 * Real.sqrt 5 := by 
    calc 
      Real.sqrt 20 = Real.sqrt (4 * 5) := by norm_num 
      _ = Real.sqrt 4 * Real.sqrt 5 := by rw [Real.sqrt_mul (by norm_num)]
      _ = 2 * Real.sqrt 5 := by 
        have h5 : Real.sqrt 4 = 2 := by 
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num 
        rw [h5] 
        all_goals linarith

  cases h3 with 
  | inl h5 =>
    left 
    rw [h4] at h5 
    linarith 
  | inr h6 =>
    right 
    rw [h4] at h6 
    linarith