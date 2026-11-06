import Mathlib

theorem algebra_95740 (x : ℝ) (hx : x ≥ 1) :
    Real.sqrt (5 * x - 1) + Real.sqrt (x - 1) = 2 ↔ x = 1 := by
  constructor
  · -- Assume Real.sqrt (5 * x - 1) + Real.sqrt (x - 1) = 2, prove x = 1
    rintro h_eq
    have h1 : Real.sqrt (5 * x - 1) ≥ 0 := by
      apply Real.sqrt_nonneg
    have h2 : Real.sqrt (x - 1) ≥ 0 := by 
      apply Real.sqrt_nonneg
    have h3 : Real.sqrt (5 * x - 1) + Real.sqrt (x - 1) = 2 := h_eq
    have h4 : (Real.sqrt (5 * x - 1) + Real.sqrt (x - 1)) ^ 2 = 4 := by
      rw [h_eq]
      norm_num
    have h5 : (Real.sqrt (5 * x - 1) + Real.sqrt (x - 1)) ^ 2 =
        (Real.sqrt (5 * x - 1)) ^ 2 + (Real.sqrt (x - 1)) ^ 2 + 2 * (Real.sqrt (5 * x - 1) * Real.sqrt (x - 1)) := by ring
    rw [h5] at h4
    have h6 : (Real.sqrt (5 * x - 1)) ^ 2 = 5 * x - 1 := by
      have h7 : x ≥ 1 := hx
      have h8 : 5 * x - 1 ≥ 0 := by linarith
      exact Real.sq_sqrt (show 0 ≤ (5 * x - 1 : ℝ) by linarith)
    have h7 : (Real.sqrt (x - 1)) ^ 2 = x - 1 := by
      have h8 : x - 1 ≥ 0 := by linarith
      exact Real.sq_sqrt (show 0 ≤ (x - 1 : ℝ) by linarith)
    rw [h6, h7] at h4
    have h8 : 3 * x + (Real.sqrt (5 * x - 1) * Real.sqrt (x - 1)) = 3 := by 
      nlinarith
    -- solving system of equations: 
    -- 1. sqrt1 + sqrt2 = 2 
    -- 2. 3 * x + sqrt1 * sqrt2 = 3 
    -- where sqrt1 = Real.sqrt (5 * x - 1), sqrt2 = Real.sqrt (x - 1)
    have h9 : Real.sqrt (5 * x - 1) = 2 := by 
      nlinarith [sq_nonneg (Real.sqrt (5 * x - 1) - 2), sq_nonneg (Real.sqrt (x - 1) - 0), 
                  Real.sqrt_nonneg (5 * x - 1), Real.sqrt_nonneg (x - 1)]
    -- solving for x from Real.sqrt (5 * x - 1) = 2
    have h6' : 5 * x - 1 = 4 := by
      calc
        5 * x - 1 = (Real.sqrt (5 * x - 1)) ^ 2 := by
          rw [Real.sq_sqrt]
          nlinarith
        _ = (2 : ℝ) ^ 2 := by
          rw [h9]
        _ = 4 := by norm_num
    -- solving x from 5 * x - 1 = 4
    have h13 : x = 1 := by
      linarith
    exact h13
  · -- Assume x = 1 prove the equation
    intro h_eq
    rw [h_eq]
    have h12 : Real.sqrt (5 * (1 : ℝ) - 1) = 2 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    have h13 : Real.sqrt ((1 : ℝ) - 1) = 0 := by 
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    rw [h12, h13]
    all_goals norm_num