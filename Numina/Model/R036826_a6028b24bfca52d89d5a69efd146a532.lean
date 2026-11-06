import Mathlib

theorem algebra_296768 (x y : ℝ) (hx : 2 - x ≥ 0) (hy : x + 3 * y - 5 ≥ 0) (h : y + 2 ≥ 0)
    (h' : 12 * y - 3 ≥ 0) (h'' : Real.sqrt (2 - x) + Real.sqrt (x + 3 * y - 5) + Real.sqrt (y + 2) =
    Real.sqrt (12 * y - 3)) :
    x = -7 ∧ y = 7 := by
  have h_eq1 : Real.sqrt (2 - x) + Real.sqrt (x + 3 * y - 5) + Real.sqrt (y + 2) = Real.sqrt (12 * y - 3) := h''

  have h_sq1 : (Real.sqrt (2 - x) + Real.sqrt (x + 3 * y - 5) + Real.sqrt (y + 2)) ^ 2 = (Real.sqrt (12 * y - 3)) ^ 2 := by 
    rw [h_eq1]
  
  have h_sq2 : (Real.sqrt (2 - x) + Real.sqrt (x + 3 * y - 5) + Real.sqrt (y + 2)) ^ 2 =
      (Real.sqrt (2 - x)) ^ 2 + (Real.sqrt (x + 3 * y - 5)) ^ 2 + (Real.sqrt (y + 2)) ^ 2 + 
      2 * (Real.sqrt (2 - x) * Real.sqrt (x + 3 * y - 5) + Real.sqrt (2 - x) * Real.sqrt (y + 2) + Real.sqrt (x + 3 * y - 5) * Real.sqrt (y + 2)) := by 
    ring
  
  have h_sq3 : (Real.sqrt (12 * y - 3)) ^ 2 = 12 * y - 3 := by
    rw [Real.sq_sqrt]
    linarith
  
  have h_sq4 : (Real.sqrt (2 - x)) ^ 2 = 2 - x := by
    rw [Real.sq_sqrt]
    linarith
  
  have h_sq5 : (Real.sqrt (x + 3 * y - 5)) ^ 2 = x + 3 * y - 5 := by
    rw [Real.sq_sqrt]
    linarith
  
  have h_sq6 : (Real.sqrt (y + 2)) ^ 2 = y + 2 := by
    rw [Real.sq_sqrt]
    linarith
  
  have h_nlinarith : x = -7 ∧ y = 7 := by
    constructor
    · -- Prove x = -7
      nlinarith [Real.sqrt_nonneg (2 - x), Real.sqrt_nonneg (x + 3 * y - 5), Real.sqrt_nonneg (y + 2), sq_nonneg (Real.sqrt (2 - x) - Real.sqrt (x + 3 * y - 5)), sq_nonneg (Real.sqrt (2 - x) - Real.sqrt (y + 2)), sq_nonneg (Real.sqrt (x + 3 * y - 5) - Real.sqrt (y + 2)), sq_nonneg (Real.sqrt (2 - x) + Real.sqrt (x + 3 * y - 5) + Real.sqrt (y + 2) - Real.sqrt (12 * y - 3)), h_sq1, h_sq3, h_sq4, h_sq5, h_sq6]
    · -- Prove y = 7
      nlinarith [Real.sqrt_nonneg (2 - x), Real.sqrt_nonneg (x + 3 * y - 5), Real.sqrt_nonneg (y + 2), sq_nonneg (Real.sqrt (2 - x) - Real.sqrt (x + 3 * y - 5)), sq_nonneg (Real.sqrt (2 - x) - Real.sqrt (y + 2)), sq_nonneg (Real.sqrt (x + 3 * y - 5) - Real.sqrt (y + 2)), sq_nonneg (Real.sqrt (2 - x) + Real.sqrt (x + 3 * y - 5) + Real.sqrt (y + 2) - Real.sqrt (12 * y - 3)), h_sq1, h_sq3, h_sq4, h_sq5, h_sq6]
  
  exact h_nlinarith