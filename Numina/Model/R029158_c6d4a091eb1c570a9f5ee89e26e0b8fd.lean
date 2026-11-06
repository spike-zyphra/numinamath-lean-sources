import Mathlib

theorem algebra_4799 : ((Real.sqrt 3) ^ (Real.sqrt 2)) ^ (Real.sqrt 2) > ((Real.sqrt 2) ^ (Real.sqrt 3)) ^ (Real.sqrt 3) := by 
  have h1 : ((Real.sqrt 3) ^ (Real.sqrt 2)) ^ (Real.sqrt 2) = (3 : ℝ) := by
    have h2 : ((Real.sqrt 3) ^ (Real.sqrt 2 : ℝ)) ^ (Real.sqrt 2 : ℝ) = (Real.sqrt 3) ^ (Real.sqrt 2 * Real.sqrt 2 : ℝ) := by 
      rw [← Real.rpow_mul]
      ring_nf
      all_goals linarith [Real.sqrt_nonneg (3 : ℝ), Real.sqrt_nonneg (2 : ℝ)]
    have h3 : Real.sqrt 2 * Real.sqrt 2 = (2 : ℝ) := by 
      calc
        Real.sqrt 2 * Real.sqrt 2 = (Real.sqrt 2) ^ 2 := by ring
        _ = (2 : ℝ) := by 
          rw [Real.sq_sqrt]
          all_goals linarith
    have h4 : Real.sqrt 3 ^ (Real.sqrt 2 * Real.sqrt 2 : ℝ) = (3 : ℝ) := by 
      rw [show Real.sqrt 2 * Real.sqrt 2 = (2 : ℝ) by linarith [h3]]
      have h5 : Real.sqrt 3 ^ (2 : ℝ) = (3 : ℝ) := by
        have h6 : Real.sqrt 3 ^ (2 : ℝ) = ((Real.sqrt 3) ^ 2 : ℝ) := by 
          norm_cast
        rw [h6]
        rw [Real.sq_sqrt]
        all_goals norm_num
      rw [h5]
    rw [h2, h4]

  have h2 : ((Real.sqrt 2) ^ (Real.sqrt 3)) ^ (Real.sqrt 3) = (2 * Real.sqrt 2 : ℝ) := by
    have h3 : ((Real.sqrt 2) ^ (Real.sqrt 3 : ℝ)) ^ (Real.sqrt 3 : ℝ) = (Real.sqrt 2) ^ (Real.sqrt 3 * Real.sqrt 3 : ℝ) := by 
      rw [← Real.rpow_mul]
      ring_nf
      all_goals linarith [Real.sqrt_nonneg (2 : ℝ), Real.sqrt_nonneg (3 : ℝ)]
    have h4 : Real.sqrt 3 * Real.sqrt 3 = (3 : ℝ) := by
      calc
        Real.sqrt 3 * Real.sqrt 3 = (Real.sqrt 3) ^ 2 := by ring
        _ = (3 : ℝ) := by 
          rw [Real.sq_sqrt]
          all_goals linarith
    have h7 : (Real.sqrt 2 : ℝ) ^ (Real.sqrt 3 * Real.sqrt 3 : ℝ) = (2 * Real.sqrt 2 : ℝ) := by
      rw [show Real.sqrt 3 * Real.sqrt 3 = (3 : ℝ) by linarith [h4]]
      -- Now we need to show: `√2 ^ 3 = 2 * √2` (as real powers/nums).
      -- First convert real power to Nat power.
      -- The original code's `h9` and `h8` were insufficient.
      have h8 : (Real.sqrt 2 : ℝ) ^ (3 : ℝ) = (2 * Real.sqrt 2 : ℝ) := by
        -- First convert to Nat power.
        have h9 : (Real.sqrt 2 : ℝ) ^ (3 : ℝ) = (Real.sqrt 2) ^ 3 := by
          norm_cast
        rw [h9]
        -- Now we need to compute `(sqrt 2)^3`.
        have h10 : (Real.sqrt 2) ^ 3 = (2 * Real.sqrt 2) := by
          calc
            (Real.sqrt 2) ^ 3 = (Real.sqrt 2) * (Real.sqrt 2) * (Real.sqrt 2) := by ring
            _ = (2) * (Real.sqrt 2) := by
              have h9 : (Real.sqrt 2 : ℝ) ^2 = (2 : ℝ) := by
                rw [Real.sq_sqrt]; norm_num 
              have h10 : (Real.sqrt 2) * (Real.sqrt 2) = (2 : ℝ) := by nlinarith [h9]
              rw [h10]
              <;> ring
            _ = (2 * Real.sqrt 2) := by ring
        -- Apply the result from h10.
        linarith [h10]
      linarith [h8]
    rw [h3, h7]

  rw [h1, h2]
  have h4 : (3 : ℝ) > (2 * Real.sqrt 2 : ℝ) := by 
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num : (0 : ℝ) < (2 : ℝ)), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num : (0 : ℝ) ≤ (2 : ℝ)), sq_nonneg (3 - 2 * Real.sqrt 2)]
  linarith [h4]