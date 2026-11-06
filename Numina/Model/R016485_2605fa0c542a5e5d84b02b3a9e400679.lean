import Mathlib

open Real

theorem algebra_100110 (x : ℝ) (hx : x^2 - 2 * x - 8 < 0) :
    logb 3 (8 + 2 * x - x^2) = 2^(x - 1) + 2^(1 - x) ↔ x = 1 := by 
  constructor
  · -- Assume logb 3 (8 + 2 * x - x^2) = 2^(x - 1) + 2^(1 - x) then x = 1
    intro h_eq
    have h1 : 8 + 2 * x - x^2 > 0 := by 
      nlinarith 
    have h2 : logb 3 (8 + 2 * x - x^2) ≤ 2 := by
      have h3 : 8 + 2 * x - x^2 ≤ 9 := by
        nlinarith [sq_nonneg (x - 1)]
      have h5 : logb 3 (9 : ℝ) = 2 := by 
        rw [logb_eq_iff_rpow_eq] <;> (norm_num)
      have h4 : logb 3 (8 + 2 * x - x^2) ≤ logb 3 (9 : ℝ) := by 
        apply logb_le_logb_of_le 
        all_goals 
          nlinarith [h1, show (9 : ℝ) > 0 by norm_num]
      linarith [h4, h5]
    have h3 : (2 : ℝ) ^ (x - 1 : ℝ) + (2 : ℝ) ^ (1 - x : ℝ) ≥ 2 := by 
      have h4 : (2 : ℝ) ^ (x - 1 : ℝ) > 0 := by positivity 
      have h5 : (2 : ℝ) ^ (1 - x : ℝ) > 0 := by positivity 
      have h6 : (2 : ℝ) ^ (x - 1 : ℝ) * ((2 : ℝ) ^ (1 - x : ℝ)) = 1 := by 
        have h7 : (2 : ℝ) ^ (x - 1 : ℝ) * ((2 : ℝ) ^ (1 - x : ℝ)) = (2 : ℝ) ^ ((x - 1 : ℝ) + (1 - x : ℝ)) := by 
          rw [← Real.rpow_add] 
          ring 
          all_goals 
            linarith 
        rw [h7] 
        have h8 : (x - 1 : ℝ) + (1 - x : ℝ) = (0 : ℝ) := by ring 
        rw [h8] 
        simp 
      nlinarith [sq_nonneg ((2 : ℝ) ^ (x - 1 : ℝ) - 1), sq_nonneg ((2 : ℝ) ^ (1 - x : ℝ) - 1),
                  mul_pos h4 h5, h6]
    have h4 : logb 3 (8 + 2 * x - x^2) = 2 := by 
      nlinarith [h_eq, h2, h3]
    have h5 : (8 + 2 * x - x^2 : ℝ) = 9 := by 
      have h6 : (8 + 2 * x - x^2 : ℝ) = (3 : ℝ) ^ (2 : ℝ) := by 
        rw [logb_eq_iff_rpow_eq] at h4 
        · -- Show that $8 + 2*x - x^2 = 3^2$
          nlinarith [h4] 
        all_goals 
          nlinarith [h1] 
      rw [show (3 : ℝ) ^ (2 : ℝ) = (9 : ℝ) by norm_num] at h6 
      linarith
    have h6 : (x - 1 : ℝ) ^ 2 = 0 := by 
      nlinarith 
    have h7 : (x - 1 : ℝ) = 0 := by 
      nlinarith 
    linarith 
  · -- Assume x = 1 then $\log_3(8+2x-x^2) = 2^{x-1} + 2^{1-x}$
    intro h_eq 
    rw [h_eq]
    have h1 : logb 3 (8 + 2 * (1 : ℝ) - (1 : ℝ)^2) = 2 := by 
      rw [show (8 + 2 * (1 : ℝ) - (1 : ℝ)^2) = (9 : ℝ) by norm_num]
      have h2 : logb 3 (9 : ℝ) = 2 := by 
        rw [logb_eq_iff_rpow_eq] <;> (norm_num)
      linarith 
    rw [h1] 
    all_goals 
      norm_num