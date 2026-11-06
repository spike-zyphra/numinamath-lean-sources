import Mathlib

theorem algebra_220924 (x : ℝ) (hx : 0 ≤ x) (h : Real.sqrt (4 * x ^ 2 + 4 * x) + 2 * x + 1 = 100) :
    x = (99 / 20) ^ 2 := by
  have h1 : Real.sqrt (4 * x ^ 2 + 4 * x) = 99 - 2 * x := by
    linarith
  
  have h2 : 0 ≤ (99 - 2 * x) := by
    linarith [Real.sqrt_nonneg (4 * x ^ 2 + 4 * x)]

  have h3 : (Real.sqrt (4 * x ^ 2 + 4 * x)) ^ 2 = (99 - 2 * x) ^ 2 := by
    rw [h1]

  have h4 : (Real.sqrt (4 * x ^ 2 + 4 * x)) ^ 2 = 4 * x ^ 2 + 4 * x := Real.sq_sqrt (by nlinarith)

  rw [h4] at h3
  
  have h5 : 4 * x ^ 2 + 4 * x = (99 - 2 * x) ^ 2 := by 
    linarith
  
  have h6 : 4 * x ^ 2 + 4 * x = 4 * x ^ 2 + 9801 - 396 * x := by 
    nlinarith [h5]

  have h7 : 4 * x = 9801 - 396 * x := by 
    nlinarith [h6]

  have h8 : 400 * x = 9801 := by 
    linarith [h7]

  have h9 : x = 9801 / 400 := by
    linarith

  rw [h9]
  norm_num