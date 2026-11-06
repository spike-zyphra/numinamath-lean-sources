import Mathlib

open Real

theorem inequalities_311051 {a b c : ℝ}
    (ha : a = sqrt 2 - 1) (hb : b = 3 - 2 * sqrt 2) (hc : c = sqrt 3 - sqrt 2) :
    a > c ∧ c > b := by
  constructor
  · -- First part: prove that a > c
    rw [ha, hc]
    have h1 : sqrt 2 > 0 := by positivity 
    have h2 : sqrt 3 > 0 := by positivity 
    nlinarith [Real.sqrt_nonneg 2, Real.sqrt_nonneg 3,
      Real.mul_self_sqrt (show (0 : ℝ) ≤ 2 by norm_num), 
      Real.mul_self_sqrt (show (0 : ℝ) ≤ 3 by norm_num), 
      Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num : ((0 : ℝ) < 2)), 
      Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num : ((0 : ℝ) < 3)), 
      sq_nonneg (sqrt 2 - sqrt 3), sq_nonneg (sqrt 3 - 2), sq_nonneg (sqrt 2 - 1), sq_nonneg (sqrt 3 - sqrt 2)]
  · -- Second part: prove that c > b
    rw [hc, hb]
    have h1 : sqrt 2 > 0 := by positivity 
    have h2 : sqrt 3 > 0 := by positivity 
    nlinarith [Real.sqrt_nonneg 2, Real.sqrt_nonneg 3,
      Real.mul_self_sqrt (show (0 : ℝ) ≤ 2 by norm_num), 
      Real.mul_self_sqrt (show (0 : ℝ) ≤ 3 by norm_num), 
      Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num : ((0 : ℝ) < 2)), 
      Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num : ((0 : ℝ) < 3)), 
      sq_nonneg (sqrt 3 - sqrt 2), sq_nonneg (sqrt 3 - 2), sq_nonneg (sqrt 2 - 1), sq_nonneg (sqrt 3 - sqrt 2)]