import Mathlib

open Real

theorem algebra_4927 (x : ℝ) (hx : x ≤ 30 ∧ x ≥ 12) :
    sqrt (x - 12) + sqrt (30 - x) ≤ 6 := by

  have h1 : x - 12 ≥ 0 := by linarith [hx.right]
  have h2 : 30 - x ≥ 0 := by linarith [hx.left]
  
  have h3 : sqrt (x - 12) ^ 2 = x - 12 := Real.sq_sqrt (by linarith)
  have h4 : sqrt (30 - x) ^ 2 = 30 - x := Real.sq_sqrt (by linarith)
  
  have h5 : sqrt (x - 12) ^ 2 + sqrt (30 - x) ^ 2 = 18 := by 
    rw [h3, h4]
    linarith
  
  nlinarith [sq_nonneg (sqrt (x - 12) - sqrt (30 - x)), sq_nonneg (sqrt (x - 12) + sqrt (30 - x)), Real.sqrt_nonneg (x - 12), Real.sqrt_nonneg (30 - x), Real.sq_sqrt (show (x - 12) ≥ 0 by linarith), Real.sq_sqrt (show (30 - x) ≥ 0 by linarith)]