import Mathlib

theorem algebra_95195 {y : ℝ} (hy : y ^ 2 ≥ 25) :
    (5 - Real.sqrt (y ^ 2 - 25)) ^ 2 = y ^ 2 - 10 * Real.sqrt (y ^ 2 - 25) := by 
  have h1 : (Real.sqrt (y ^ 2 - 25)) ^ 2 = y ^ 2 - 25 := by 
    rw [Real.sq_sqrt]
    linarith 
  nlinarith [h1, Real.sqrt_nonneg (y ^ 2 - 25)]