import Mathlib

theorem algebra_228706 (x : ℝ) (hx : 2 * x ^ 2 - 2 * x + 1 ≥ 0) :
    10 * x - 6 + x ^ 2 = Real.sqrt (2 * x ^ 2 - 2 * x + 1) * Real.sqrt (36 + (x + 4) ^ 2) ↔ x = 4 := by 
  constructor 
  · -- Assume the equation, prove x = 4
    rintro h_eq
    have h1 : Real.sqrt (2 * x ^ 2 - 2 * x + 1) * Real.sqrt (36 + (x + 4) ^ 2) ≥ 0 := by 
      positivity
    -- Now we need to show from h_eq that x=4.
    -- First, let's establish that 10 * x - 6 + x ^ 2 ≥ 0.
    have h2 : 10 * x - 6 + x ^ 2 ≥ 0 := by 
      by_contra h 
      push_neg at h
      have h3 : Real.sqrt (2 * x ^ 2 - 2 * x + 1) * Real.sqrt (36 + (x + 4) ^ 2) ≥ 0 := h1 
      have h4 : 10 * x - 6 + x ^ 2 < (0 : ℝ) := by linarith
      have h5 : Real.sqrt (2 * x ^ 2 - 2 * x + 1) * Real.sqrt (36 + (x + 4) ^ 2) ≥ 0 := h1
      have h6 : 10 * x - 6 + x ^ 2 = Real.sqrt (2 * x ^ 2 - 2 * x + 1) * Real.sqrt (36 + (x + 4) ^ 2) := by linarith [h_eq] 
      nlinarith 
    -- Now squaring is possible.
    have h6 : (10 * x - 6 + x ^ 2) ^ 2 = (Real.sqrt (2 * x ^ 2 - 2 * x + 1) * Real.sqrt (36 + (x + 4) ^ 2)) ^ 2 := by
      have h8 : Real.sqrt (2 * x ^ 2 - 2 * x + 1) * Real.sqrt (36 + (x + 4) ^ 2) = (10 * x - 6 + x ^ 2) := by linarith [h_eq]
      rw [h8]
      all_goals nlinarith 
    -- Now we can expand the RHS.
    have h7 : (Real.sqrt (2 * x ^ 2 - 2 * x + 1) * Real.sqrt (36 + (x + 4) ^ 2)) ^ 2 = (2 * x ^ 2 - 2 * x + 1) * (36 + (x + 4) ^ 2) := by 
      calc
        (Real.sqrt (2 * x ^ 2 - 2 * x + 1) * Real.sqrt (36 + (x + 4) ^ 2)) ^ 2 
          = (Real.sqrt (2 * x ^ 2 - 2 * x + 1)) ^ 2 * (Real.sqrt (36 + (x + 4) ^ 2)) ^ 2 := by 
            ring 
        _ = (2 * x ^ 2 - 2 * x + 1) * (Real.sqrt (36 + (x + 4) ^ 2)) ^ 2 := by 
          have h1a : (Real.sqrt (2 * x ^ 2 - 2 * x + 1)) ^ 2 = (2 * x ^ 2 - 2 * x + 1) := by 
            apply Real.sq_sqrt 
            linarith 
          rw [h1a] 
        _ = (2 * x ^ 2 - 2 * x + 1) * (36 + (x + 4) ^ 2) := by 
          have h1b : (Real.sqrt (36 + (x + 4) ^ 2)) ^ 2 = (36 + (x + 4) ^ 2) := by 
            apply Real.sq_sqrt 
            nlinarith [sq_nonneg (x + 4)]
          rw [h1b]
    -- Now equate the two expressions for (10 * x - 6 + x ^ 2) ^ 2.
    have h8 : (10 * x - 6 + x ^ 2) ^ 2 = (2 * x ^ 2 - 2 * x + 1) * (36 + (x + 4) ^ 2) := by
      nlinarith [h6, h7] 
    -- Now solve the polynomial.
    have h9 : (x - 4) ^ 2 * (x + 1) ^ 2 = 0 := by 
      nlinarith [sq_nonneg (x ^ 2 - 3 * x - 4), sq_nonneg (x - 4), sq_nonneg (x + 1)]
    cases' (mul_eq_zero.mp h9) with h10 h11 
    · -- Case (x - 4) ^ 2 = 0 
      have h12 : (x - 4) ^ 2 = 0 := by 
        exact h10 
      have h13 : x - 4 = 0 := by 
        apply pow_eq_zero 
        exact h12 
      linarith 
    · -- Case (x + 1) ^ 2 = 0 
      have h14 : (x + 1) ^ 2 = 0 := by 
        exact h11 
      have h15 : x + 1 = 0 := by 
        apply pow_eq_zero 
        exact h14 
      nlinarith [Real.sqrt_nonneg (2 * x ^ 2 - 2 * x + 1), Real.sqrt_nonneg (36 + (x + 4) ^ 2), 
        Real.sq_sqrt (show (2 * x ^ 2 - 2 * x + 1 : ℝ) ≥ 0 by linarith), 
        Real.sq_sqrt (show (36 + (x + 4) ^ 2 : ℝ) ≥ 0 by nlinarith)
      ]
  · -- Backward implication: if x = 4, then the equation holds 
    intro h_eq 
    rw [show x = 4 by linarith] 
    have h11 : Real.sqrt (2 * (4 : ℝ) ^ 2 - 2 * (4 : ℝ) + 1) = (5 : ℝ) := by 
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num 
    have h12 : Real.sqrt (36 + (4 + 4 : ℝ) ^ 2) = (10 : ℝ) := by 
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num 
    rw [h11, h12] 
    all_goals norm_num