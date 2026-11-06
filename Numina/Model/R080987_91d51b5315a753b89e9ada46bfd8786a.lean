import Mathlib

theorem algebra_299298 (x y : ℝ) (h : 0 ≤ x + 2 ∧ 0 ≤ y - 5) (h' : Real.sqrt (x + 2) + Real.sqrt (y - 5) = 6) :
    x + 2 * y ≥ 32 ∧ x + 2 * y ≤ 80 := by 
  have h1 : Real.sqrt (x + 2) ≥ 0 := by 
    apply Real.sqrt_nonneg 
  have h2 : Real.sqrt (y - 5) ≥ 0 := by 
    apply Real.sqrt_nonneg 
  have hab : Real.sqrt (x + 2) + Real.sqrt (y - 5) = 6 := h'
  have h3 : Real.sqrt (x + 2) ≤ 6 := by 
    linarith [show Real.sqrt (y - 5) ≥ 0 by positivity] 
  have h4 : Real.sqrt (y - 5) ≤ 6 := by 
    linarith [show Real.sqrt (x + 2) ≥ 0 by positivity] 
  have eq1 : x + 2 = (Real.sqrt (x + 2)) ^ 2 := by 
    rw [Real.sq_sqrt] 
    linarith [h.1] 
  have eq2 : y - 5 = (Real.sqrt (y - 5)) ^ 2 := by 
    rw [Real.sq_sqrt] 
    linarith [h.2] 
  constructor 
  · -- Proof of the minimum 
    nlinarith [sq_nonneg (Real.sqrt (x + 2) - 4), sq_nonneg (Real.sqrt (y - 5) - 2), sq_nonneg (Real.sqrt (x + 2) - Real.sqrt (y - 5) - 2), Real.sq_sqrt (show 0 ≤ (x + 2 : ℝ) by linarith [h.1]), Real.sq_sqrt (show 0 ≤ (y - 5 : ℝ) by linarith [h.2])] 
  · -- Proof of the maximum 
    nlinarith [sq_nonneg (Real.sqrt (x + 2)), sq_nonneg (Real.sqrt (y - 5)), sq_nonneg (Real.sqrt (x + 2) - 0), sq_nonneg (Real.sqrt (y - 5) - 6), sq_nonneg (Real.sqrt (x + 2) - 6), sq_nonneg (Real.sqrt (y - 5)), Real.sq_sqrt (show 0 ≤ (x + 2 : ℝ) by linarith [h.1]), Real.sq_sqrt (show 0 ≤ (y - 5 : ℝ) by linarith [h.2])]