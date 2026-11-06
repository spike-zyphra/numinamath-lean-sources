import Mathlib

theorem algebra_19792 (a : ℝ) (h : a + 1 ≥ 0):
    Real.sqrt (4 + Real.sqrt (16 + 16 * a)) + Real.sqrt (1 + Real.sqrt (1 + a)) = 6 ↔ a = 8 := by
  constructor
  · -- Assume the equation holds, prove a = 8
    intro h_eq
    have h1 : Real.sqrt (4 + Real.sqrt (16 + 16 * a)) = 2 * Real.sqrt (1 + Real.sqrt (1 + a)) := by
      have h2 : Real.sqrt (16 + 16 * a) = 4 * Real.sqrt (1 + a) := by
        have h3 : Real.sqrt (16 + 16 * a) = Real.sqrt (16 * (1 + a)) := by
          ring_nf
        rw [h3]
        have h4 : Real.sqrt (16 * (1 + a)) = Real.sqrt (16) * Real.sqrt (1 + a) := by
          rw [Real.sqrt_mul]
          all_goals linarith
        rw [h4]
        have h5 : Real.sqrt (16 : ℝ) = (4 : ℝ) := by
          rw [Real.sqrt_eq_cases]
          norm_num
        rw [h5]
      have h6 : (4 + Real.sqrt (16 + 16 * a) ) = 4 * (1 + Real.sqrt (1 + a)) := by
        rw [h2]
        linarith
      rw [h6]
      have h7 : Real.sqrt (4 * (1 + Real.sqrt (1 + a)) ) = Real.sqrt (4) * Real.sqrt (1 + Real.sqrt (1 + a)) := by
        rw [Real.sqrt_mul]
        all_goals
          positivity
      rw [h7]
      have h8 : Real.sqrt (4 : ℝ) = (2 : ℝ) := by
        rw [Real.sqrt_eq_cases]
        norm_num
      rw [h8]
    -- Now simplifying the equation
    have h3 : Real.sqrt (1 + Real.sqrt (1 + a)) = 2 := by
      nlinarith [Real.sqrt_nonneg (4 + Real.sqrt (16 + 16 * a)), Real.sqrt_nonneg (1 + Real.sqrt (1 + a)), Real.sq_sqrt (show (4 + Real.sqrt (16 + 16 * a) : ℝ) ≥ 0 by positivity), Real.sq_sqrt (show (1 + Real.sqrt (1 + a) : ℝ) ≥ 0 by positivity), h1, h_eq]
    -- Solving for Real.sqrt (1 + a)
    have h4 : (1 + Real.sqrt (1 + a) ) = 4 := by
      calc
        (1 + Real.sqrt (1 + a) ) = (Real.sqrt (1 + Real.sqrt (1 + a)) ) ^ 2 := by
          rw [Real.sq_sqrt]
          positivity
        _ = (2 : ℝ) ^ 2 := by
          rw [h3]
        _ = (4 : ℝ) := by
          norm_num
    -- Solving for Real.sqrt (1 + a)
    have h5 : Real.sqrt (1 + a) = 3 := by
      nlinarith
    -- Solving for a
    have h6 : (1 + a) = 9 := by
      calc
        (1 + a) = (Real.sqrt (1 + a)) ^ 2 := by
          rw [Real.sq_sqrt]
          linarith
        _ = (3 : ℝ) ^ 2 := by
          rw [h5]
        _ = (9 : ℝ) := by
          norm_num
    -- Final computation to get a = 8
    nlinarith
  · -- Assume a = 8, prove the equation
    intro h_eq
    rw [h_eq]
    have h1 : Real.sqrt (4 + Real.sqrt (16 + 16 * (8 : ℝ))) = (4 : ℝ) := by
      have h2 : Real.sqrt (16 + 16 * (8 : ℝ)) = (12 : ℝ) := by
        rw [Real.sqrt_eq_cases]
        norm_num
      rw [h2]
      rw [Real.sqrt_eq_cases]
      norm_num
    have h3 : Real.sqrt (1 + Real.sqrt (1 + (8 : ℝ) ) ) = (2 : ℝ) := by
      have h4 : Real.sqrt (1 + (8 : ℝ) ) = (3 : ℝ) := by
        rw [Real.sqrt_eq_cases]
        norm_num
      rw [h4]
      rw [Real.sqrt_eq_cases]
      norm_num
    rw [h1, h3]
    all_goals norm_num