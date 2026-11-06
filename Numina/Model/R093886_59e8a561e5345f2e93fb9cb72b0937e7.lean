import Mathlib

theorem algebra_236847 (x : ℝ) (hx : abs (x^2 - 100) = 10 * x + 90) :
    x = 5 + Real.sqrt 215 ∨ x = -5 + Real.sqrt 35 := by
  by_cases h : x^2 - 100 ≥ 0 
  · -- case x^2 - 100 ≥ 0
    rw [abs_of_nonneg h] at hx
    have h1 : x^2 - 10 * x - 190 = 0 := by linarith
    have h2 : (x - (5 + Real.sqrt 215)) * (x - (5 - Real.sqrt 215)) = 0 := by
      nlinarith [Real.sqrt_pos.mpr (show (0:ℝ) < 215 by norm_num : (0:ℝ) < 215), Real.sq_sqrt (show (0:ℝ) ≤ 215 by norm_num : (0:ℝ) ≤ 215)]
    cases' (mul_eq_zero.mp h2) with h3 h4 
    · -- h3: x - (5 + sqrt 215) = 0
      left
      linarith
    · -- h4: x - (5 - sqrt 215) = 0 
      nlinarith [Real.sqrt_pos.mpr (show (0:ℝ) < 215 by norm_num : (0:ℝ) < 215), Real.sq_sqrt (show (0:ℝ) ≤ 215 by norm_num : (0:ℝ) ≤ 215), sq_nonneg (x - 5), sq_nonneg (x + 5)]
  · -- case x^2 - 100 < 0 
    rw [abs_of_neg (lt_of_not_ge h)] at hx
    have h1 : x^2 + 10 * x - 10 = 0 := by linarith
    have h2 : (x - (-5 + Real.sqrt 35)) * (x - (-5 - Real.sqrt 35)) = 0 := by
      nlinarith [Real.sqrt_pos.mpr (show (0:ℝ) < 35 by norm_num : (0:ℝ) < 35), Real.sq_sqrt (show (0:ℝ) ≤ 35 by norm_num : (0:ℝ) ≤ 35)]
    cases' (mul_eq_zero.mp h2) with h3 h4 
    · -- h3 : x - (-5 + Real.sqrt 35) = 0
      right
      linarith
    · -- h4 : x - (-5 - Real.sqrt 35) = 0 
      nlinarith [Real.sqrt_pos.mpr (show (0:ℝ) < 35 by norm_num : (0:ℝ) < 35), Real.sq_sqrt (show (0:ℝ) ≤ 35 by norm_num : (0:ℝ) ≤ 35), sq_nonneg (x + 5), sq_nonneg (x - 5)]