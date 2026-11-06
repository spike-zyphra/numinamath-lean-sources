import Mathlib

theorem algebra_275493 (x : ℝ) (hx : x ≥ 3) :
    Real.sqrt (x + 4) - Real.sqrt (x - 3) + 1 ≠ 0 := by 
  by_contra h
  have h1 : Real.sqrt (x + 4) - Real.sqrt (x - 3) + 1 = 0 := by 
    linarith
  have h2 : Real.sqrt (x + 4) = Real.sqrt (x - 3) - 1 := by linarith
  have h3 : Real.sqrt (x + 4) ≥ 0 := by 
    apply Real.sqrt_nonneg
  have h4 : Real.sqrt (x - 3) ≥ 0 := by 
    apply Real.sqrt_nonneg 
  have h5 : Real.sqrt (x - 3) ≥ 1 := by
    nlinarith [h2, h3, h4]
  have h6 : (Real.sqrt (x + 4)) ^ 2 = (Real.sqrt (x - 3) - 1) ^ 2 := by 
    rw [h2]
  have h7 : (Real.sqrt (x + 4)) ^ 2 = (Real.sqrt (x - 3) ^ 2 - 2 * Real.sqrt (x - 3) + 1) := by 
    nlinarith 
  have h8 : (Real.sqrt (x + 4)) ^ 2 = x + 4 := by 
    rw [Real.sq_sqrt]
    linarith 
  have h9 : (Real.sqrt (x - 3)) ^ 2 = x - 3 := by 
    rw [Real.sq_sqrt]
    linarith 
  rw [h8] at h7
  rw [h9] at h7
  have h11 : Real.sqrt (x - 3) = -3 := by 
    nlinarith 
  have h13 : Real.sqrt (x - 3) ≥ 0 := by
    apply Real.sqrt_nonneg 
  nlinarith