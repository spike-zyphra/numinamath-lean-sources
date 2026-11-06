import Mathlib

open Real

theorem algebra_193478 {x y : ℝ} (hx : x > 0) (hy : y > 0)
    (h1 : x + y = 13) (h2 : logb 4 x + logb 4 y = 1 + logb 4 10) :
    (x = 5 ∧ y = 8) ∨ (x = 8 ∧ y = 5) := by

  have h3 : logb 4 x + logb 4 y = logb 4 (x * y) := by
    rw [logb_mul (by linarith) (by linarith)]
  
  have h4 : (1 + logb 4 10) = logb 4 40 := by
    have h5 : logb 4 (40 : ℝ) = logb 4 4 + logb 4 10 := by 
      rw [show (40 : ℝ) = 4 * 10 by norm_num]
      rw [logb_mul (by norm_num) (by norm_num)]
    have h6 : logb 4 (4 : ℝ) = 1 := by
      norm_num [logb_eq_iff_rpow_eq]
    linarith [h5, h6]
  
  have h7 : logb 4 (x * y) = logb 4 40 := by
    linarith [h2, h3, h4]

  have h8 : x * y = 40 := by 
    have h9 : x * y > 0 := by 
      positivity
    have h10 : (40 : ℝ) > 0 := by 
      norm_num
    have h11 : logb 4 (x * y) = logb 4 40 := h7
    have h12 : x * y = 40 := by 
      apply logb_injOn_pos (by norm_num) (Set.mem_Ioi.mpr h9) (Set.mem_Ioi.mpr h10) h11
      all_goals norm_num at *
      all_goals linarith
    linarith

  have h9 : y = 13 - x := by
    linarith
  
  rw [h9] at h8
  have h10 : x ^ 2 - 13 * x + 40 = 0 := by 
    nlinarith
  
  have h11 : (x - 5) * (x - 8) = 0 := by 
    nlinarith
  
  cases' (mul_eq_zero.mp h11) with h12 h13
  · -- Case where x = 5, then y = 8
    have hx5 : x = 5 := by 
      linarith
    have hy8 : y = 8 := by 
      nlinarith [h9, hx5]
    left
    exact ⟨hx5, hy8⟩
  
  · -- Case where x = 8, then y = 5
    have hx8 : x = 8 := by 
      linarith
    have hy5 : y = 5 := by 
      nlinarith [h9, hx8]
    right
    exact ⟨hx8, hy5⟩