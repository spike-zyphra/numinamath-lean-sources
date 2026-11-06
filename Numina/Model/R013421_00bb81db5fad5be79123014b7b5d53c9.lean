import Mathlib

theorem algebra_220794 (x : ℝ) : (x^2 + x + 2)^(x^2 + x + 1) = 9 ↔
    x = (-1 + Real.sqrt 5) / 2 ∨ x = (-1 - Real.sqrt 5) / 2 := by 
  constructor
  · -- Forward direction: If (x^2 + x + 2)^(x^2 + x + 1) = 9, then x = (-1 ±√5)/2
    intro h_eq
    have h1 : x^2 + x + 2 > 0 := by 
      nlinarith [sq_nonneg (x + 1 / 2)]
    have h2 : (x^2 + x + 1) * (Real.log (x^2 + x + 2)) = Real.log 9 := by
      have h4 : Real.log ((x^2 + x + 2) ^ (x^2 + x + 1)) = Real.log 9 := by
        rw [h_eq]
      have h3 : Real.log ((x^2 + x + 2) ^ (x^2 + x + 1)) = (x^2 + x + 1) * Real.log (x^2 + x + 2) := by
        rw [Real.log_rpow]
        all_goals nlinarith
      linarith [h4, h3]
    have h3 : x^2 + x + 1 = (2 : ℝ) := by
      by_cases h5 : x^2 + x + 1 < (2 : ℝ)
      · -- Case where x^2 + x + 1 < 2
        have h6 : x^2 + x + 1 < (2 : ℝ) := h5
        have h61 : x^2 + x + 2 < (3 : ℝ) := by nlinarith
        have h62 : x^2 + x + 2 > (1 : ℝ) := by nlinarith [sq_nonneg (x + 1 / 2)]
        have h8 : Real.log (x^2 + x + 2) < Real.log (3 : ℝ) := by 
          apply Real.log_lt_log
          all_goals nlinarith
        have h9 : 0 < Real.log (x^2 + x + 2) := by 
          apply Real.log_pos
          nlinarith
        -- Now we need to show it's contradiction 
        have h64 : (x^2 + x + 1) * Real.log (x^2 + x + 2) < Real.log 9 := by 
          have h8' : Real.log 9 = (2 * Real.log (3 : ℝ)) := by 
            calc 
              Real.log 9 = Real.log (3 ^ 2 : ℝ) := by norm_num 
              _ = 2 * Real.log (3 : ℝ) := by simp [Real.log_pow]
          nlinarith [show 0 ≤ (x^2 + x + 1 : ℝ) by nlinarith, Real.log_pos (show (3 : ℝ) > 1 by norm_num)]
        -- The original equality can't hold from h64
        have h7 : Real.log 9 = (x^2 + x + 1) * Real.log (x^2 + x + 2) := by 
          linarith [h2]
        linarith
      · -- Now that left is dis proven, move to right
        by_cases h6 : x^2 + x + 1 > (2 : ℝ)
        · -- Now handle the case > 2
          have h7 : x^2 + x + 1 > (2 : ℝ) := h6
          have h71 : x^2 + x + 2 > (3 : ℝ) := by
            nlinarith
          -- For greater value, the Real.log will also be higher
          have h9 : Real.log (x^2 + x + 2) > Real.log (3 : ℝ) := by
            apply Real.log_lt_log
            all_goals nlinarith
          -- Now to derive a real contradiction
          have h73 : (x^2 + x + 1) * Real.log (x^2 + x + 2) > Real.log 9 := by 
            have h8' : Real.log 9 = (2 * Real.log (3 : ℝ)) := by 
              calc 
                Real.log 9 = Real.log (3 ^ 2 : ℝ) := by norm_num 
                _ = 2 * Real.log (3 : ℝ) := by simp [Real.log_pow]
            nlinarith [show 0 ≤ (x^2 + x + 1 : ℝ) by nlinarith, Real.log_pos (show (3 : ℝ) > 1 by norm_num), show 0 < Real.log (x^2 + x + 2) by apply Real.log_pos; nlinarith [sq_nonneg (x + 1 / 2)]]
          -- The original equality can't hold from h73
          have h72 : Real.log 9 = (x^2 + x + 1) * Real.log (x^2 + x + 2) := by 
            linarith [h2]
          linarith 
        · -- The only solution left is =
          linarith 
    -- Now we get a specific value 
    have h4 : x^2 + x - 1 = 0 := by
      nlinarith 
    have : x = (-1 + Real.sqrt 5) / 2 ∨ x = (-1 - Real.sqrt 5) / 2 := by 
      have h6 : x^2 + x - 1 = 0 := h4 
      have h70 : (x - (-1 + Real.sqrt 5) / 2) * (x - (-1 - Real.sqrt 5) / 2) = 0 := by 
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 5 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
      cases' (mul_eq_zero.1 h70) with h60 h50
      · -- Either root 
        left 
        linarith 
      · -- Or the other root 
        right 
        linarith 
    assumption 
  · -- Reverse direction: If x = (-1 ±√5)/2, then (x^2 +x+2)^(x^2+x+1)=9
    rintro (h_eq | h_eq)
    · -- First solution 
      rw [h_eq] 
      -- Verify the first solution $(-1 + Real.sqrt 5)/2$ 
      -- Explicitly calculating the powers $x^2 +x +2$ and exponent 
      have h10 : ((-1 + Real.sqrt 5 : ℝ) / 2) ^ 2 + ((-1 + Real.sqrt 5 : ℝ) / 2) + 1 = (2 : ℝ) := by
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 5 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
      have h11 : ((-1 + Real.sqrt 5 : ℝ) / 2) ^ 2 + ((-1 + Real.sqrt 5 : ℝ) / 2) + 2 = (3 : ℝ) := by
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 5 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
      rw [show ((-1 + Real.sqrt 5 : ℝ) / 2) ^ 2 + ((-1 + Real.sqrt 5 : ℝ) / 2) + 2 = (3 : ℝ) by linarith [h11]]
      rw [show ((-1 + Real.sqrt 5 : ℝ) / 2) ^ 2 + ((-1 + Real.sqrt 5 : ℝ) / 2) + 1 = (2 : ℝ) by linarith [h10]]
      all_goals norm_num 
      all_goals nlinarith 
    · -- Second solution 
      rw [h_eq] 
      -- Verify the second solution $(-1 - Real.sqrt 5)/2$ 
      -- Explicitly calculating the powers $x^2 +x +2$ and exponent 
      have h10 : ((-1 - Real.sqrt 5 : ℝ) / 2) ^ 2 + ((-1 - Real.sqrt 5 : ℝ) / 2) + 1 = (2 : ℝ) := by
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 5 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
      have h11 : ((-1 - Real.sqrt 5 : ℝ) / 2) ^ 2 + ((-1 - Real.sqrt 5 : ℝ) / 2) + 2 = (3 : ℝ) := by
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 5 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
      rw [show ((-1 - Real.sqrt 5 : ℝ) / 2) ^ 2 + ((-1 - Real.sqrt 5 : ℝ) / 2) + 2 = (3 : ℝ) by linarith [h11]]
      rw [show ((-1 - Real.sqrt 5 : ℝ) / 2) ^ 2 + ((-1 - Real.sqrt 5 : ℝ) / 2) + 1 = (2 : ℝ) by linarith [h10]]
      all_goals norm_num
      all_goals nlinarith 
    all_goals linarith