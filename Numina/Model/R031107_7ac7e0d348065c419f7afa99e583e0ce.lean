import Mathlib

open Real

theorem algebra_9788 {x : ℝ} (hx : 0 < x) :
    logb 7 7 + logb 7 (3 * x ^ 3 + 108) - 2 = 3 * logb 7 x ↔ x = 3 := by
  constructor
  · -- Assume the equation holds, prove x = 3
    intro h_eq
    have h1 : logb 7 7 = 1 := by
      rw [logb_eq_iff_rpow_eq] <;> (norm_num)
    
    rw [h1] at h_eq
    have h3 : logb 7 (3 * x ^ 3 + 108) = 3 * logb 7 x + 1 := by
      linarith
    have h4 : logb 7 (3 * x ^ 3 + 108) = logb 7 (x^3) + 1 := by
      have h5 : 3 * logb 7 x = logb 7 (x^3) := by
        simp [logb_pow]
      linarith [h3, h5]
    
    have h5 : logb 7 (3 * x ^ 3 + 108) - logb 7 (x^3) = 1 := by
      have h4' : logb 7 (3 * x ^ 3 + 108) = logb 7 (x^3) + 1 := h4
      linarith
    have h6 : logb 7 (3 * x ^ 3 + 108) - logb 7 (x^3) = logb 7 ((3 * x ^ 3 + 108) / (x^3)) := by 
      rw [← logb_div (by positivity) (by positivity)]
    
    rw [h6] at h5
    have h7 : (3 * x ^ 3 + 108) / (x^3) = 7 := by
      have h9 : logb 7 ((3 * x ^ 3 + 108) / (x^3)) = 1 := h5
      have h10 : (7 : ℝ) ^ (logb 7 ((3 * x ^ 3 + 108) / (x^3)) : ℝ) = ( (3 * x ^ 3 + 108) / (x^3) ) := by
        rw [Real.rpow_logb]
        all_goals
          try { nlinarith }
          try { positivity }
      rw [h9] at h10
      have h12 : (7 : ℝ) ^ (1 : ℝ) = 7 := by
        norm_num
      rw [h12] at h10
      linarith
    
    field_simp at h7
    have h8 : x ^ 3 = 27 := by
      nlinarith
    have h9 : x = 3 := by
      have h10 : x ^ 3 - (27 : ℝ) = 0 := by
        linarith
      have h11 : (x - 3) * (x ^ 2 + 3 * x + 9) = 0 := by
        nlinarith
      cases' (mul_eq_zero.1 h11) with h12 h13
      · -- Case 1: x - 3 = 0
        linarith
      · -- Case 2: x^2 + 3 * x + 9 = 0
        nlinarith [sq_nonneg (x + 3 / 2), sq_nonneg (x - 3 / 2)]
    
    exact h9
  · -- Assume x = 3, prove the equation
    intro h_eq
    rw [h_eq]
    have h1 : logb 7 7 = 1 := by
      rw [logb_eq_iff_rpow_eq] <;> (norm_num)
    
    have h3 : (3 * (3 : ℝ) ^ 3 + 108 : ℝ) = 189 := by
      norm_num
    have h4 : logb 7 (3 * (3 : ℝ) ^ 3 + 108) = logb 7 189 := by
      rw [h3]
    
    have h5 : logb 7 189 = logb 7 27 + 1 := by
      have h5 : (189 : ℝ) = (27 : ℝ) * (7 : ℝ) := by norm_num
      rw [h5]
      have h6 : logb 7 (27 * (7 : ℝ)) = logb 7 27 + logb 7 7 := by 
        rw [logb_mul (by norm_num) (by norm_num)]
      rw [h6]
      have h7 : logb 7 7 = 1 := h1
      linarith
    have h8 : logb 7 27 = 3 * logb 7 (3 : ℝ) := by
      have h9 : (27 : ℝ) = (3 : ℝ) ^ 3 := by norm_num
      rw [h9]
      have h10 : logb 7 ((3 : ℝ) ^ 3) = 3 * logb 7 (3 : ℝ) := by
        simp [logb_pow]
      linarith
    linarith [h1, h4, h5, h8]