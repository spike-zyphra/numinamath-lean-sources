import Mathlib

open Real
open scoped BigOperators

theorem inequalities_111130 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0)
  (h : a^2 + b^2 = c^2) :
  a + b ≤ c * sqrt 2 := by
    have h1 : (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by
      nlinarith [sq_nonneg (a - b)]
    have h2 : (a + b) ^ 2 ≤ 2 * c^2 := by
      nlinarith [h, h1]
    have h3 : (a + b) ≥ 0 := by linarith
    have h4 : c * sqrt 2 ≥ 0 := by 
      have hc2 : c > 0 := hc
      have hsqrt2 : sqrt 2 > 0 := by positivity
      positivity
    have h5 : (c * sqrt 2) ^ 2 = 2 * c^2 := by
      calc
        (c * sqrt 2) ^ 2 = c^2 * (sqrt 2) ^ 2 := by ring
        _ = c^2 * 2 := by rw [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
        _ = 2 * c^2 := by ring
    nlinarith [Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), 
      h3, h4, h2, h5, 
      sq_nonneg (a + b - c * sqrt 2)]