import Mathlib

theorem algebra_244593 (x : ℝ) (hx : 8 * x - 5 ≥ 0 ∧ 8 * x - 6 ≥ 0 ∧ 5 * x - 2 ≥ 0 ∧ 5 * x - 3 ≥ 0) :
    Real.sqrt (8 * x - 5) - Real.sqrt (8 * x - 6) = Real.sqrt (5 * x - 2) - Real.sqrt (5 * x - 3) ↔ x = 1 := by 
  constructor
  · -- Assume the equation holds, prove x = 1
    intro h_eq
    rcases hx with ⟨h1, h2, h3, h4⟩
    have h5 : Real.sqrt (8 * x - 5) + Real.sqrt (5 * x - 3) = Real.sqrt (8 * x - 6) + Real.sqrt (5 * x - 2) := by 
      linarith [h_eq]
    have h6 : (Real.sqrt (8 * x - 5) + Real.sqrt (5 * x - 3)) ^ 2 = (Real.sqrt (8 * x - 6) + Real.sqrt (5 * x - 2)) ^ 2 := by 
      rw [h5]
    have h7 : Real.sqrt (8 * x - 5) ^ 2 = 8 * x - 5 := Real.sq_sqrt (by linarith)
    have h8 : Real.sqrt (8 * x - 6) ^ 2 = 8 * x - 6 := Real.sq_sqrt (by linarith)
    have h9 : Real.sqrt (5 * x - 2) ^ 2 = 5 * x - 2 := Real.sq_sqrt (by linarith)
    have h10 : Real.sqrt (5 * x - 3) ^ 2 = 5 * x - 3 := Real.sq_sqrt (by linarith)
    have h11 : Real.sqrt (8 * x - 5) * Real.sqrt (5 * x - 3) = Real.sqrt (8 * x - 6) * Real.sqrt (5 * x - 2) := by
      nlinarith [h6, h7, h8, h9, h10]
    have h12 : (8 * x - 5) * (5 * x - 3) = (8 * x - 6) * (5 * x - 2) := by
      nlinarith [Real.sqrt_nonneg (8 * x - 5), Real.sqrt_nonneg (8 * x - 6), Real.sqrt_nonneg (5 * x - 2), Real.sqrt_nonneg (5 * x - 3), h11, Real.sq_sqrt (show (8 * x - 5 : ℝ) ≥ 0 by linarith), Real.sq_sqrt (show (8 * x - 6 : ℝ) ≥ 0 by linarith), Real.sq_sqrt (show (5 * x - 2 : ℝ) ≥ 0 by linarith), Real.sq_sqrt (show (5 * x - 3 : ℝ) ≥ 0 by linarith)]
    nlinarith 
  · -- Assume x = 1, prove the equation
    intro h_eq
    rw [h_eq]
    have h1 : Real.sqrt (8 * (1 : ℝ) - 5) = Real.sqrt 3 := by norm_num 
    have h2 : Real.sqrt (8 * (1 : ℝ) - 6) = Real.sqrt 2 := by norm_num 
    have h3 : Real.sqrt (5 * (1 : ℝ) - 2) = Real.sqrt 3 := by norm_num 
    have h4 : Real.sqrt (5 * (1 : ℝ) - 3) = Real.sqrt 2 := by norm_num 
    rw [h1, h2, h3, h4]
    all_goals linarith