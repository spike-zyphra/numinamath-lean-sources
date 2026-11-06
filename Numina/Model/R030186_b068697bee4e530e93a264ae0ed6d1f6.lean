import Mathlib

open Real

theorem algebra_187655 {x : ℝ} (hx : x > 2) :
    logb 5 (x - 2) + logb (sqrt 5) (x ^ 3 - 2) + logb 0.2 (x - 2) = 4 ↔ x = 3 := by
  constructor
  · -- Assume the equation holds, prove x = 3
    intro h_eq
    have h1 : logb (sqrt 5) (x ^ 3 - 2) = 2 * logb 5 (x ^ 3 - 2) := by 
      have h2 : logb (sqrt 5) (x ^ 3 - 2) = (logb 5 (x ^ 3 - 2)) / (logb 5 (sqrt 5)) := by 
        field_simp [logb]
      have h3 : logb 5 (sqrt 5) = 1 / 2 := by
        have h4 : sqrt 5 = (5 : ℝ) ^ (1 / 2 : ℝ) := by 
          rw [Real.sqrt_eq_rpow]
        rw [h4]
        have h5 : logb 5 ((5 : ℝ) ^ (1 / 2 : ℝ)) = (1 / 2 : ℝ) := by 
          rw [logb_rpow]
          all_goals norm_num
        linarith 
      rw [h2, h3] 
      <;> ring 
    have h3 : logb (0.2 : ℝ) (x - 2) = - logb 5 (x - 2) := by 
      have h4 : logb (0.2 : ℝ) (x - 2) = (logb 5 (x - 2)) / (logb 5 (0.2 : ℝ)) := by 
        field_simp [logb]
      have h5 : logb 5 (0.2 : ℝ) = -1 := by
        rw [Real.logb_eq_iff_rpow_eq] <;> norm_num 
      rw [h4, h5]
      field_simp
    rw [h1, h3] at h_eq
    have h4 : 2 * logb 5 (x ^ 3 - 2) = 4 := by
      linarith
    have h5 : logb 5 (x ^ 3 - 2) = 2 := by 
      linarith
    have h6 : x ^ 3 - 2 = (5 : ℝ) ^ (2 : ℝ) := by 
      rw [logb_eq_iff_rpow_eq] at h5
      · -- Show that x ^ 3 - 2 = 5 ^ 2 
        linarith
      all_goals 
      have h9 : x ^ 3 - 2 > 0 := by
        nlinarith [sq_nonneg (x ^ 2 - 1)]
      all_goals nlinarith [sq_nonneg (x ^ 2 - 1)]
    have h7 : x ^ 3 = 27 := by 
      nlinarith [h6]
    have h8 : x = 3 := by
      have h9 : x ^ 3 - 27 = 0 := by 
        nlinarith [h7]
      have h10 : (x - 3) * (x ^ 2 + 3 * x + 9) = 0 := by 
        nlinarith [h9]
      cases' (mul_eq_zero.mp h10) with h11 h12 
      · -- Case x - 3 = 0 
        linarith
      · -- Case x ^ 2 + 3 * x + 9 = 0 
        nlinarith [sq_nonneg (x + 3 / 2)]
    exact h8
  · -- Assume x = 3, prove the equation 
    intro h_eq 
    rw [h_eq]
    have h1 : logb (5 : ℝ) (3 - 2 : ℝ) = 0 := by 
      norm_num [logb_one]
    have h2 : logb (sqrt 5) ((3 : ℝ) ^ 3 - 2 : ℝ) = 4 := by 
      rw [show (3 : ℝ) ^ 3 - 2 = (25 : ℝ) by norm_num]
      have h3 : logb (sqrt 5) (25 : ℝ) = 4 := by 
        have h4 : logb (sqrt 5) (25 : ℝ) = (logb (5 : ℝ) (25 : ℝ)) / (logb (5 : ℝ) (sqrt 5 : ℝ)) := by 
          field_simp [logb]
        have h5 : logb (5 : ℝ) (25 : ℝ) = 2 := by 
          rw [logb_eq_iff_rpow_eq] <;> norm_num
        have h6 : logb (5 : ℝ) (sqrt 5 : ℝ) = (1 / 2 : ℝ) := by 
          have h7 : sqrt 5 = (5 : ℝ) ^ (1 / 2 : ℝ) := by 
            rw [Real.sqrt_eq_rpow]
          rw [h7]
          have h8 : logb (5 : ℝ) ((5 : ℝ) ^ (1 / 2 : ℝ)) = (1 / 2 : ℝ) := by 
            rw [logb_rpow]
            all_goals norm_num 
          linarith
        rw [h4, h5, h6]
        all_goals norm_num 
      linarith 
    have h4 : logb (0.2 : ℝ) (3 - 2 : ℝ) = 0 := by 
      norm_num [logb_one]
    rw [h1, h2, h4]
    all_goals norm_num