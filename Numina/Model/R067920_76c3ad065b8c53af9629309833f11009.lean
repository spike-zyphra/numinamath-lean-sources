import Mathlib

theorem algebra_234370 (x : ℝ) :
    abs (x ^ 2 - 100) = 10 * x + 90 ↔ x = 5 + Real.sqrt 215 ∨ x = -5 + Real.sqrt 35 := by
  constructor
  · -- First direction: if equation holds, prove the two roots
    intro h_eq
    by_cases h : x ^ 2 - 100 ≥ 0
    · -- Case 1: x^2 - 100 ≥ 0
      have h1 : abs (x ^ 2 - 100) = x ^ 2 - 100 := abs_of_nonneg h
      rw [h1] at h_eq
      have h_eq2 : (x - (5 + Real.sqrt 215)) * (x - (5 - Real.sqrt 215)) = 0 := by
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 215 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 215 by norm_num)]
      cases' (mul_eq_zero.mp h_eq2) with h3 h4 
      · -- First case: valid root
        left 
        linarith 
      · -- Second case: invalid root
        have h5 : x = 5 - Real.sqrt 215 := by linarith
        have h6 : (x) ^ 2 < 100 := by 
          rw [h5] 
          nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 215 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 215 by norm_num)]
        nlinarith 
    · -- Case 2: x^2 - 100 < 0
      have h2 : abs (x ^ 2 - 100) = -(x ^ 2 - 100) := abs_of_neg (lt_of_not_ge h)
      rw [h2] at h_eq
      have h_eq2 : (x - (-5 + Real.sqrt 35)) * (x - (-5 - Real.sqrt 35)) = 0 := by
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 35 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 35 by norm_num)]
      cases' (mul_eq_zero.mp h_eq2) with h6 h7 
      · -- First case: valid root
        right 
        linarith 
      · -- Second case: invalid root
        have h8 : x = -5 - Real.sqrt 35 := by linarith
        have h9 : (x) ^ 2 ≥ 100 := by 
          rw [h8] 
          nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 35 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 35 by norm_num)]
        nlinarith 
  · -- Second direction: prove that the two roots satisfy the equation
    rintro (h | h)
    · -- Case where x = 5 + Real.sqrt 215
      rw [h]
      have h3 : (5 + Real.sqrt 215) ^ 2 - 100 ≥ 0 := by
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 215 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 215 by norm_num)]
      rw [abs_of_nonneg h3] 
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 215 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 215 by norm_num)]
    · -- Case where x = -5 + Real.sqrt 35
      rw [h]
      have h3 : (-5 + Real.sqrt 35) ^ 2 - 100 < 0 := by
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 35 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 35 by norm_num)]
      rw [abs_of_neg h3]
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 35 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 35 by norm_num)]