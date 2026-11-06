import Mathlib

theorem algebra_186977 (x : ℝ) (hx : x ≥ -2) (h : Real.sqrt (x + 2) + Real.sqrt (3 * x + 8) = Real.sqrt (2 * x + 6)) :
    x = -2 := by
  have h1 : Real.sqrt (x + 2) ≥ 0 := by positivity
  have h2 : Real.sqrt (3 * x + 8) ≥ 0 := by positivity
  have h3 : Real.sqrt (2 * x + 6) ≥ 0 := by positivity
  
  have h4 : (Real.sqrt (x + 2) + Real.sqrt (3 * x + 8)) ^ 2 = Real.sqrt (2 * x + 6) ^ 2 := by
    rw [h]
  
  have h5 : (Real.sqrt (x + 2) + Real.sqrt (3 * x + 8)) ^ 2 = (Real.sqrt (x + 2)) ^ 2 + (Real.sqrt (3 * x + 8)) ^ 2 + 2 * (Real.sqrt (x + 2) * Real.sqrt (3 * x + 8)) := by ring
  
  have h6 : Real.sqrt (2 * x + 6) ^ 2 = 2 * x + 6 := by
    rw [Real.sq_sqrt]
    have h_nonneg : 2 * x + 6 ≥ 0 := by linarith
    linarith

  have h_nonneg1 : x + 2 ≥ 0 := by linarith [hx]
  have h7 : (Real.sqrt (x + 2)) ^ 2 = x + 2 := by
    rw [Real.sq_sqrt]
    linarith

  have h_nonneg2 : 3 * x + 8 ≥ 0 := by
    linarith [hx]

  have h8 : (Real.sqrt (3 * x + 8)) ^ 2 = 3 * x + 8 := by
    rw [Real.sq_sqrt]
    linarith
  
  have h9 : Real.sqrt (x + 2) * Real.sqrt (3 * x + 8) = Real.sqrt ((x + 2) * (3 * x + 8)) := by 
    rw [← Real.sqrt_mul]
    all_goals 
    linarith
  
  rw [h5, h7, h8, h9] at h4
  rw [h6] at h4
  
  have h10 : Real.sqrt ((x + 2) * (3 * x + 8)) = -x - 2 := by
    nlinarith
  
  have h14 : Real.sqrt ((x + 2) * (3 * x + 8)) ^ 2 = ((x + 2) * (3 * x + 8)) := Real.sq_sqrt (by nlinarith)

  have h13 : (-x - 2) ^ 2 = (x + 2) * (3 * x + 8) := by 
    have h14' : Real.sqrt ((x + 2) * (3 * x + 8)) = -x - 2 := h10
    nlinarith [Real.sqrt_nonneg ((x + 2) * (3 * x + 8)), sq_nonneg (-x - 2), h14]

  have h14 : 2 * x^2 + 10 * x + 12 = 0 := by
    nlinarith [h13]

  have h15 : (x + 2) * (2 * x + 6) = 0 := by
    nlinarith

  cases' (mul_eq_zero.mp h15) with h17 h18
  
  · -- x + 2 = 0, so x = -2
    linarith
  
  · -- 2 * x + 6 = 0, so x = -3, but x ≥ -2, so contradiction
    have h19 : x = -3 := by
      linarith
  
    linarith