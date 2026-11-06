import Mathlib

theorem algebra_7253 {x : ℝ} (hx : x ≠ 0) (h : x - 1/x = 3) : x + 1/x = √13 ∨ x + 1/x = -√13 := by
  have h1 : (x - 1/x) ^ 2 = 9 := by 
    rw [h]
    norm_num
  have h2 : x ^ 2 + 1 / x ^ 2 = 11 := by 
    have h3 : (x - 1/x) ^ 2 = x^2 - 2 + 1 / x ^ 2 := by 
      field_simp
      ring
    rw [h3] at h1
    linarith
  have h3 : (x + 1 / x) ^ 2 = 13 := by 
    have h4 : (x + 1 / x) ^ 2 = x ^ 2 + 2 + 1 / x ^ 2 := by 
      field_simp
      ring
    have h5 : x ^ 2 + 1 / x ^ 2 = 11 := h2
    linarith [h4, h5]
  have h5 : ((x + 1 / x) - √13) * ((x + 1 / x) + √13) = 0 := by
    nlinarith [Real.sqrt_pos.mpr (show (13 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (13 : ℝ) by norm_num)]
  cases' (mul_eq_zero.mp h5) with h6 h7
  · -- Case h6 : (x + 1/x) - √13 = 0 
    left 
    have h8 : x + 1/x = √13 := by linarith
    exact h8
  · -- Case h7 : (x + 1/x) + √13 = 0 
    right 
    have h8 : x + 1/x = -√13 := by linarith
    exact h8