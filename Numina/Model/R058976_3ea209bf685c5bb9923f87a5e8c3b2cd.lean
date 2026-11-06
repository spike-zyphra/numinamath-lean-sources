import Mathlib

theorem algebra_153681 (x : ℝ) (hx : 1 ≤ x) : Real.sqrt (x - 1) * Real.sqrt (2 * x + 6) = x + 3 ↔ x = 5 := by 
  constructor
  · -- Forward implication: if the equation holds, show x = 5
    intro h_eq 
    have h1 : Real.sqrt (x - 1) ≥ 0 := Real.sqrt_nonneg (x - 1)
    have h2 : Real.sqrt (2 * x + 6) ≥ 0 := Real.sqrt_nonneg (2 * x + 6)
    have h3 : Real.sqrt (x - 1) * Real.sqrt (2 * x + 6) ≥ 0 := by 
      apply mul_nonneg 
      · linarith
      · linarith
    have h4 : (Real.sqrt (x - 1) * Real.sqrt (2 * x + 6)) ^ 2 = (x + 3) ^ 2 := by 
      rw [h_eq]
    have h5 : ((Real.sqrt (x - 1) * Real.sqrt (2 * x + 6)) ^ 2) = (x - 1) * (2 * x + 6) := by
      calc
        ((Real.sqrt (x - 1) * Real.sqrt (2 * x + 6)) ^ 2) 
          = (Real.sqrt (x - 1)) ^ 2 * (Real.sqrt (2 * x + 6)) ^ 2 := by 
            ring
        _ = (x - 1) * (2 * x + 6) := by
          have h1' : (Real.sqrt (x - 1)) ^ 2 = x - 1 := by 
            apply Real.sq_sqrt 
            linarith
          have h2' : (Real.sqrt (2 * x + 6)) ^ 2 = 2 * x + 6 := by 
            apply Real.sq_sqrt 
            linarith
          rw [h1', h2']
    have h6 : (x + 3) ^ 2 = x^2 + 6 * x + 9 := by 
      ring
    rw [h5] at h4 
    have h7 : (x - 1) * (2 * x + 6) = x^2 + 6 * x + 9 := by 
      linarith [h4, h6]
    have h8 : x^2 - 2 * x - 15 = 0 := by 
      linarith [h7]
    have h9 : (x - 5) * (x + 3) = 0 := by 
      linarith [h8]
    cases' (mul_eq_zero.mp h9) with h10 h11
    · -- Case 1: x - 5 = 0, so x = 5 
      linarith 
    · -- Case 2: x + 3 = 0, so x = -3, which contradicts 1 ≤ x 
      linarith 
  · -- Backward implication: if x = 5, prove the equation
    intro h_eq 
    rw [h_eq]
    have h5 : Real.sqrt (5 - 1 : ℝ) = 2 := by 
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    have h6 : Real.sqrt (2 * (5 : ℝ) + 6) = 4 := by 
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    rw [h5, h6]
    all_goals norm_num