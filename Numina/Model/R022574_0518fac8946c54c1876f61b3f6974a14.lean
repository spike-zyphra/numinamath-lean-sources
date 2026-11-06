import Mathlib

open Real

theorem algebra_150305 (x : ℝ) (hx : x > 0) :
    x ^ (logb 3 (27 * x ^ 2)) = x ^ 9 / 81 ↔ x = 3 ∨ x = 9 := by
  constructor
  · -- Assume x^(logb 3 (27 * x ^ 2)) = x^9 / 81, prove x = 3 ∨ x = 9
    intro h_eq
    have h1 : logb 3 (27 * x ^ 2) = 3 + 2 * logb 3 x := by
      have h2 : logb 3 (27 * x ^ 2) = logb 3 (27) + logb 3 (x ^ 2) := by 
        rw [logb_mul (by norm_num) (by positivity)]
      have h3 : logb 3 (27 : ℝ) = 3 := by
        rw [logb_eq_iff_rpow_eq] <;> norm_num
      have h4 : logb 3 (x ^ 2) = 2 * logb 3 x := by 
        simp [logb_pow]
      rw [h2, h3, h4]
    rw [h1] at h_eq
    have h3 : logb 3 (x ^ (3 + 2 * logb 3 x)) = logb 3 (x ^ 9 / 81) := by 
      rw [h_eq]
    have h4 : logb 3 (x ^ (3 + 2 * logb 3 x)) = (3 + 2 * logb 3 x) * logb 3 x := by
      rw [logb_rpow_eq_mul_logb_of_pos]
      all_goals linarith
    have h5 : logb 3 (x ^ 9 / 81) = (9 * logb 3 x - 4) := by
      have h6 : logb 3 (x ^ 9 / 81) = logb 3 (x ^ 9) - logb 3 (81 : ℝ) := by 
        rw [logb_div (by positivity) (by norm_num)]
      have h7 : logb 3 (x ^ 9) = 9 * logb 3 x := by
        simp [logb_pow]
      have h8 : logb 3 (81 : ℝ) = 4 := by
        rw [logb_eq_iff_rpow_eq] <;> norm_num
      rw [h6, h7, h8]
    rw [h4, h5] at h3
    have h6 : 2 * (logb 3 x) ^ 2 - 6 * (logb 3 x) + 4 = 0 := by 
      nlinarith
    have h7 : (logb 3 x - 1) * (logb 3 x - 2) = 0 := by 
      nlinarith
    cases' (mul_eq_zero.mp h7) with h8 h9
    · -- case 1
      have h8' : logb 3 x = 1 := by 
        linarith
      have h10 : x = 3 := by 
        rw [logb_eq_iff_rpow_eq] at h8'
        · -- Show that x = 3
          nlinarith
        all_goals linarith
      left
      exact h10
    · -- case 2
      have h9' : logb 3 x = 2 := by 
        linarith
      have h11 : x = 9 := by 
        rw [logb_eq_iff_rpow_eq] at h9'
        · -- Show that x = 9
          nlinarith
        all_goals linarith
      right
      exact h11
  · -- Assume x = 3 ∨ x = 9, prove x ^ (logb 3 (27 * x ^ 2)) = x ^ 9 / 81
    intro h_eq
    rcases h_eq with (rfl | rfl)
    · -- Case x = 3
      have h1 : logb 3 (27 * (3 : ℝ) ^ 2) = 5 := by 
        have h2 : 27 * (3 : ℝ) ^ 2 = (3 : ℝ) ^ 5 := by 
          norm_num
        rw [h2]
        have h3 : logb 3 ((3 : ℝ) ^ 5) = 5 := by 
          simp [logb_pow]
        exact h3
      rw [h1]
      norm_num
    · -- Case x = 9
      have h1 : logb 3 (27 * (9 : ℝ) ^ 2) = 7 := by 
        have h2 : 27 * (9 : ℝ) ^ 2 = (3 : ℝ) ^ 7 := by 
          norm_num
        rw [h2]
        have h3 : logb 3 ((3 : ℝ) ^ 7) = 7 := by 
          simp [logb_pow]
        exact h3
      rw [h1]
      norm_num