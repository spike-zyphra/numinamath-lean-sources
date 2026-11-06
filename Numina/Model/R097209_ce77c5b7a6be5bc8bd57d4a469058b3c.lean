import Mathlib

open Real
open scoped BigOperators

theorem inequalities_36333 (a b c : ℝ) (ha : 1 < a) (hb : 1 < b)
  (hc : c = sqrt (a^2 + b^2)) :
  a + b ≤ c * sqrt 2 := by 
  have h1 : c = sqrt (a^2 + b^2) := hc
  rw [h1]
  have h2 : (sqrt (a^2 + b^2) * sqrt 2) = sqrt ((a^2 + b^2) * 2) := by 
    rw [← Real.sqrt_mul (by positivity)]
    all_goals norm_num
  rw [h2]
  
  have h6 : (a + b) ^ 2 ≤ (a^2 + b^2) * 2 := by 
    linarith [sq_nonneg (a - b)]
  
  have h7 : a + b ≤ Real.sqrt ((a^2 + b^2) * 2) := by 
    have h8 : Real.sqrt ((a + b) ^ 2) = a + b := by 
      apply Real.sqrt_sq (show (a + b) ≥ 0 by linarith)
    have h9 : Real.sqrt ((a + b) ^ 2) ≤ Real.sqrt ((a^2 + b^2) * 2) := by 
      apply Real.sqrt_le_sqrt
      linarith
    linarith [h8, h9]
  
  linarith