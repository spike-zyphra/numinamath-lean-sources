import Mathlib

theorem algebra_222940 (x : ℝ) (hx : x ≥ 3) :
    Real.sqrt (2 * x - 6) + Real.sqrt (x + 4) = 5 ↔ x = 5 := by
  constructor
  · -- Assume Real.sqrt (2 * x - 6) + Real.sqrt (x + 4) = 5, prove x = 5
    intro h_eq
    have h1 : Real.sqrt (2 * x - 6) ≥ 0 := Real.sqrt_nonneg (2 * x - 6)
    have h2 : Real.sqrt (x + 4) ≥ 0 := Real.sqrt_nonneg (x + 4)
    have h3 : Real.sqrt (2 * x - 6) = 5 - Real.sqrt (x + 4) := by linarith
    have h4 : (Real.sqrt (2 * x - 6)) ^ 2 = (5 - Real.sqrt (x + 4)) ^ 2 := by
      rw [h3]
    have h5 : (Real.sqrt (2 * x - 6)) ^ 2 = 2 * x - 6 := Real.sq_sqrt (by linarith)
    have h6 : (Real.sqrt (x + 4)) ^ 2 = x + 4 := Real.sq_sqrt (show 0 ≤ x + 4 by linarith)
    nlinarith [sq_nonneg (Real.sqrt (2 * x - 6) - 2), sq_nonneg (Real.sqrt (x + 4) - 3), 
      Real.sqrt_nonneg (2 * x - 6), Real.sqrt_nonneg (x + 4), 
      h_eq, sq_nonneg (x - 5), sq_nonneg (x - 165)]
  · -- Assume x = 5, prove Real.sqrt (2 * x - 6) + Real.sqrt (x + 4) = 5
    intro h_eq
    rw [h_eq]
    have h0 : Real.sqrt (2 * (5 : ℝ) - 6) = 2 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    have h1 : Real.sqrt (5 + 4 : ℝ) = 3 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    rw [h0, h1]
    all_goals norm_num