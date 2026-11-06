import Mathlib

open Real

theorem algebra_141697 {x : ℝ} (hx : x > 0) :
    sqrt (x ^ logb 10 (sqrt x)) = 10 ↔ x = 100 ∨ x = 1 / 100 := by
  constructor
  · -- Assume sqrt (x ^ logb 10 (sqrt x)) = 10 prove x = 100 ∨ x = 1 / 100
    intro h
    have h1 : x ^ logb 10 (sqrt x) = 100 := by 
      calc 
        x ^ logb 10 (sqrt x) = (sqrt (x ^ logb 10 (sqrt x))) ^ 2 := by
          rw [Real.sq_sqrt]
          positivity 
        _ = 10 ^ 2 := by
          rw [h] 
        _ = 100 := by norm_num
    have h2 : logb 10 (x ^ logb 10 (sqrt x)) = logb 10 100 := by 
      rw [h1] 
    have h3 : logb 10 (x ^ logb 10 (sqrt x)) = logb 10 (sqrt x) * logb 10 x := by 
      rw [logb_rpow_eq_mul_logb_of_pos] 
      all_goals linarith 
    have h4 : logb 10 100 = 2 := by 
      have h5 : logb 10 100 = 2 := by 
        rw [logb_eq_iff_rpow_eq] <;> norm_num 
      rw [h5] 
    have h5 : logb 10 (sqrt x) = (1 / 2) * logb 10 x := by 
      have h6 : logb 10 (sqrt x) = logb 10 (x ^ (1 / 2 : ℝ)) := by 
        have : sqrt x = x ^ (1 / 2 : ℝ) := by 
          rw [Real.sqrt_eq_rpow] 
        rw [this] 
      have h7 : logb 10 (x ^ (1 / 2 : ℝ)) = (1 / 2 : ℝ) * logb 10 x := by 
        rw [logb_rpow_eq_mul_logb_of_pos] 
        all_goals linarith 
      rw [h6, h7] 
    rw [h3, h5, h4] at h2
    have h6 : (logb 10 x) ^ 2 = 4 := by
      nlinarith 
    have h7 : logb 10 x = 2 ∨ logb 10 x = -2 := by 
      have h10 : (logb 10 x - 2) * (logb 10 x + 2) = 0 := by 
        nlinarith [h6] 
      cases' (mul_eq_zero.mp h10) with h11 h12 
      · left 
        linarith 
      · right 
        linarith 
    rcases h7 with (h8 | h8)
    · -- Case h8 : logb 10 x = 2
      have h8a : x = 100 := by
        have h9 : x = (10 : ℝ) ^ (logb 10 x : ℝ) := by
          field_simp [hx]
        rw [h9, h8]
        norm_num
      tauto 
    · -- Case h8 : logb 10 x = -2
      have h8a : x = 1 / 100 := by 
        have h9 : x = (10 : ℝ) ^ (logb 10 x : ℝ) := by 
          field_simp [hx]
        rw [h9, h8]
        norm_num 
      tauto
  · -- Assume x = 100 ∨ x = 1 / 100 prove sqrt (x ^ logb 10 (sqrt x)) = 10 
    rintro (h | h)
    · -- Case x = 100 
      rw [h] 
      have h4 : logb 10 (sqrt (100 : ℝ)) = (1 : ℝ) := by 
        have h5 : sqrt (100 : ℝ) = (10 : ℝ) := by
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        rw [h5] 
        have h6 : logb 10 (10 : ℝ) = (1 : ℝ) := by 
          norm_num [logb_eq_iff_rpow_eq]
        linarith 
      have h7 : (100 : ℝ) ^ logb 10 (sqrt (100 : ℝ)) = (100 : ℝ) := by 
        rw [h4] 
        norm_num 
      have h8 : sqrt ((100 : ℝ) ^ logb 10 (sqrt (100 : ℝ)) ) = (10 : ℝ) := by
        rw [h7] 
        have h9 : sqrt (100 : ℝ) = (10 : ℝ) := by 
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num 
        rw [h9] 
      exact_mod_cast h8 
    · -- Case x = 1 / 100 
      rw [h] 
      have h4 : logb 10 (sqrt (1 / 100 : ℝ)) = (-1 : ℝ) := by 
        have h5 : sqrt (1 / 100 : ℝ) = (1 / 10 : ℝ) := by
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num 
        rw [h5] 
        have h6 : logb 10 (1 / 10 : ℝ) = (-1 : ℝ) := by 
          have h7 : logb 10 (1 / 10 : ℝ) = logb 10 (1 : ℝ) - logb 10 (10 : ℝ) := by 
            field_simp [logb_div]
          have h8 : logb 10 (1 : ℝ) = (0 : ℝ) := by 
            norm_num [logb_one] 
          have h9 : logb 10 (10 : ℝ) = (1 : ℝ) := by 
            norm_num [logb_eq_iff_rpow_eq]
          rw [h7, h8, h9] 
          all_goals norm_num 
        linarith 
      have h7 : (1 / 100 : ℝ) ^ logb 10 (sqrt (1 / 100 : ℝ)) = (100 : ℝ) := by 
        rw [h4] 
        norm_num 
      have h8 : sqrt ((1 / 100 : ℝ) ^ logb 10 (sqrt (1 / 100 : ℝ)) ) = (10 : ℝ) := by
        rw [h7] 
        have h9 : sqrt (100 : ℝ) = (10 : ℝ) := by 
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num 
        rw [h9] 
      exact_mod_cast h8 
      all_goals try positivity