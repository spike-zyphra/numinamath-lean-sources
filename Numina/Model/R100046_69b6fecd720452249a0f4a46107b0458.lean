import Mathlib

open Real

theorem algebra_10979 {f : ℝ → ℝ}
    (h : ∀ x, x ≤ 2 → f x = 3 ^ x)
    (h' : ∀ x, x > 2 → f x = f (x - 1)) :
    f (2 + logb 3 2) = 6 := by 
  -- We first show that 2 + log_3 2 > 2
  have h1 : 2 + logb 3 2 > 2 := by 
    have h2 : logb 3 2 > 0 := by 
      apply logb_pos
      all_goals norm_num
    linarith
  have h2 : f (2 + logb 3 2) = f (1 + logb 3 2) := by 
    rw [h' (2 + logb 3 2) h1]
    ring_nf
  -- Need to compute f(1 + log_3 2)
  -- We check if 1 + log_3 2 ≤ 2
  have h3 : 1 + logb 3 2 ≤ 2 := by
    have h4 : logb 3 2 < 1 := by 
      have h5 : logb 3 2 < logb 3 3 := by 
        apply Real.logb_lt_logb 
        all_goals norm_num 
      have h6 : logb 3 3 = 1 := by 
        rw [logb_self_eq_one]
        all_goals norm_num 
      linarith 
    linarith 
  have h4 : f (1 + logb 3 2) = (3 : ℝ) ^ (1 + logb 3 2) := by 
    apply h
    linarith 
  rw [h2, h4] 
  -- Now need to compute 3^(1 + log_3 2)
  -- Using property: a^(b + c) = a^b * a^c
  -- Then 3^(1 + log_3 2) = 3^1 * 3^log_3 2 = 3 * 2 = 6
  have h5 : (3 : ℝ) ^ (1 + logb 3 2) = (3 : ℝ) * (3 : ℝ) ^ (logb 3 2) := by 
    rw [Real.rpow_add]
    ring_nf
    all_goals norm_num 
  -- Then 3^log_3 2 = 2
  have h6 : (3 : ℝ) ^ (logb 3 2) = (2 : ℝ) := by 
    rw [Real.rpow_logb]
    all_goals norm_num 
  rw [h5, h6] 
  norm_num