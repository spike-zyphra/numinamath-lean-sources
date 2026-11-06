import Mathlib

theorem algebra_325320 (x : ℝ) :
    2 * x + 1 + x * Real.sqrt (x ^ 2 + 2) +
    (x + 1) * Real.sqrt (x ^ 2 + 2 * x + 3) = 0 ↔ x = -1 / 2 := by
  constructor
  · -- Forward direction: if the equation holds, then x = -1/2
    intro h
    by_cases h6 : x < -1 / 2
    · -- Assume x < -1/2
      by_cases h9 : x < -1
      · -- Assume x < -1
        -- Then $x+1 < 0$ and $x < 0$.
        have h4a : x < -1 := h9
        have h5a : x + 1 < 0 := by linarith
        have h6a : (x + 1) * Real.sqrt (x ^ 2 + 2 * x + 3) < 0 := by
          have h7a : x + 1 < 0 := h5a
          have h8a : Real.sqrt (x ^ 2 + 2 * x + 3) > 0 := by
            have h9a : x ^ 2 + 2 * x + 3 > 0 := by nlinarith [sq_nonneg (x + 1)]
            have h10a : Real.sqrt (x ^ 2 + 2 * x + 3) > 0 := by
              apply Real.sqrt_pos.mpr
              linarith
            linarith
          nlinarith
        have h7a : x * Real.sqrt (x ^ 2 + 2) < 0 := by
          have h8a : x < 0 := by linarith
          have h9a : Real.sqrt (x ^ 2 + 2) > 0 := by
            have h5a : x ^ 2 + 2 > 0 := by nlinarith
            have h6a : Real.sqrt (x ^ 2 + 2) > 0 := by
              apply Real.sqrt_pos.mpr
              linarith
            linarith
          nlinarith
        have h6b : 2 * x + 1 < 0 := by nlinarith
        nlinarith [Real.sqrt_nonneg (x ^ 2 + 2), Real.sqrt_nonneg (x ^ 2 + 2 * x + 3), 
                  Real.sq_sqrt (show x ^ 2 + 2 ≥ 0 by nlinarith), 
                  Real.sq_sqrt (show x ^ 2 + 2 * x + 3 ≥ 0 by nlinarith)]
      · -- Assume -1 ≤ x < -1/2
        have h6b : -1 ≤ x := by linarith
        have h7b : x < -1 / 2 := by linarith
        have h8b : x < 0 := by nlinarith
        have h9b : x * Real.sqrt (x ^ 2 + 2) < 0 := by
          have h8a : x < 0 := h8b
          have h9a : Real.sqrt (x ^ 2 + 2) > 0 := by
            have h5a : x ^ 2 + 2 > 0 := by nlinarith
            have h6a : Real.sqrt (x ^ 2 + 2) > 0 := by
              apply Real.sqrt_pos.mpr
              linarith
            linarith
          nlinarith
        have h7b : x + 1 ≥ 0 := by linarith
        have h7c : (x + 1) * Real.sqrt (x ^ 2 + 2 * x + 3) ≥ 0 := by
          have h8c : x + 1 ≥ 0 := h7b
          have h9c : Real.sqrt (x ^ 2 + 2 * x + 3) ≥ 0 := Real.sqrt_nonneg (x ^ 2 + 2 * x + 3)
          nlinarith
        have h6c : 2 * x + 1 < 0 := by nlinarith
        nlinarith [Real.sqrt_nonneg (x ^ 2 + 2), Real.sqrt_nonneg (x ^ 2 + 2 * x + 3), 
                  Real.sq_sqrt (show x ^ 2 + 2 ≥ 0 by nlinarith), 
                  Real.sq_sqrt (show x ^ 2 + 2 * x + 3 ≥ 0 by nlinarith)]
    · -- Assume x ≥ -1/2
      have h6a : x ≥ -1 / 2 := by linarith
      by_cases h6 : x > -1 / 2
      · -- Assume x > -1/2
        by_cases h8 : x ≥ 0
        · -- Assume x ≥ 0
          have h9 : x * Real.sqrt (x ^ 2 + 2) ≥ 0 := by
            nlinarith [show 0 ≤ x by linarith, Real.sqrt_nonneg (x ^ 2 + 2)]
          have h10 : (x + 1) * Real.sqrt (x ^ 2 + 2 * x + 3) ≥ 0 := by
            nlinarith [show 0 ≤ x + 1 by nlinarith, Real.sqrt_nonneg (x ^ 2 + 2 * x + 3)]
          have h6c : 2 * x + 1 > 0 := by nlinarith
          nlinarith [Real.sqrt_nonneg (x ^ 2 + 2), Real.sqrt_nonneg (x ^ 2 + 2 * x + 3), 
                    Real.sq_sqrt (show x ^ 2 + 2 ≥ 0 by nlinarith), 
                    Real.sq_sqrt (show x ^ 2 + 2 * x + 3 ≥ 0 by nlinarith)]
        · -- Assume -1/2 < x < 0
          have h8a : -1 / 2 < x := by linarith
          have h8b : x < 0 := by nlinarith
          have h8c : x + 1 > 0 := by linarith
          have h9 : x * Real.sqrt (x ^ 2 + 2) < 0 := by
            have h8a : x < 0 := h8b
            have h9a : Real.sqrt (x ^ 2 + 2) > 0 := by
              have h5a : x ^ 2 + 2 > 0 := by nlinarith
              have h6a : Real.sqrt (x ^ 2 + 2) > 0 := by
                apply Real.sqrt_pos.mpr
                linarith
              linarith
            nlinarith
          have h10 : (x + 1) * Real.sqrt (x ^ 2 + 2 * x + 3) > 0 := by
            have h7a : x + 1 > 0 := h8c
            have h8a : Real.sqrt (x ^ 2 + 2 * x + 3) > 0 := by
              have h9a : x ^ 2 + 2 * x + 3 > 0 := by nlinarith [sq_nonneg (x + 1)]
              have h10a : Real.sqrt (x ^ 2 + 2 * x + 3) > 0 := by
                apply Real.sqrt_pos.mpr
                linarith
              linarith
            nlinarith
          have h6c : 2 * x + 1 > 0 := by nlinarith
          nlinarith [Real.sqrt_nonneg (x ^ 2 + 2), Real.sqrt_nonneg (x ^ 2 + 2 * x + 3), 
                    Real.sq_sqrt (show x ^ 2 + 2 ≥ 0 by nlinarith), 
                    Real.sq_sqrt (show x ^ 2 + 2 * x + 3 ≥ 0 by nlinarith)]
      · -- Assume x = -1/2
        -- This is the only possibility left, so x = -1/2.
        have h6a : x = -1 / 2 := by linarith
        linarith
  · -- Backward direction: if x = -1/2, then the equation holds
    intro h
    rw [h]
    have h1 : Real.sqrt ((-1 / 2 : ℝ) ^ 2 + 2) = 3 / 2 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    have h2 : Real.sqrt ((-1 / 2 : ℝ) ^ 2 + 2 * (-1 / 2) + 3) = 3 / 2 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    rw [h1, h2]
    norm_num