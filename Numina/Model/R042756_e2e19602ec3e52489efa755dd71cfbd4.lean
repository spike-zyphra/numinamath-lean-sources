import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_146996 {x : ℝ} (hx : 0 < x) :
    abs (logb 2 x) + 1 ≥ logb 2 (4 * x) ↔ x ≤ sqrt 2 / 2 := by
  have h1 : logb 2 (4 * x) = logb 2 4 + logb 2 x := by
    rw [logb_mul (by linarith) (by linarith)]
  have h2 : logb 2 4 = 2 := by
    rw [logb_eq_iff_rpow_eq] <;> norm_num
  have h3 : logb 2 (4 * x) = 2 + logb 2 x := by
    rw [h1, h2]
  rw [h3]
  constructor
  · -- Assume abs (logb 2 x) + 1 ≥ 2 + logb 2 x, prove x ≤ sqrt 2 / 2
    intro h
    by_cases h4 : logb 2 x ≥ 0
    · -- Case where logb 2 x ≥ 0
      have h5 : abs (logb 2 x) = logb 2 x := by
        rw [abs_of_nonneg h4]
      rw [h5] at h
      -- h : logb 2 x + 1 ≥ 2 + logb 2 x
      have h6 : (logb 2 x + 1 ≥ 2 + logb 2 x) := by linarith
      -- This simplifies to 1 >= 2 which is false.
      exfalso
      linarith
    · -- Case where logb 2 x < 0
      have h6 : abs (logb 2 x) = -logb 2 x := by
        rw [abs_of_neg (show logb 2 x < (0 : ℝ) by linarith)]
      rw [h6] at h
      -- Now `h` is: -logb 2 x + 1 ≥ 2 + logb 2 x
      -- Simplify to: -2 logb 2 x + 1 - 2 ≥ 2 + logb 2 x
      -- Rearranged to: -2 * logb 2 x + 1 - 2 ≥ 0 or -2 * logb 2 x -1 ≥ 0
      -- This is equivalent to logb 2 x ≤ -1/2
      have h7 : logb 2 x ≤ -1 / 2 := by linarith
      -- Now we need to convert from `logb 2 x ≤ -1/2` to a bound on x
      have h8 : x ≤ (2 : ℝ) ^ (- (1 / 2 : ℝ)) := by
        have h9 : x = (2 : ℝ) ^ (logb 2 x : ℝ) := by
          field_simp
        rw [h9]
        have h10 : logb 2 x ≤ (- (1 / 2 : ℝ) ) := by linarith
        have h11 : (2 : ℝ) ^ (logb 2 x : ℝ) ≤ (2 : ℝ) ^ (- (1 / 2 : ℝ) ) := by
          apply Real.rpow_le_rpow_of_exponent_le
          all_goals linarith
        linarith
      have h9 : (2 : ℝ) ^ (- (1 / 2 : ℝ)) = Real.sqrt 2 / 2 := by
        have h10 : (2 : ℝ) ^ (- (1 / 2 : ℝ)) = Real.sqrt 2 / 2 := by
          have h11 : (2 : ℝ) ^ (- (1 / 2 : ℝ)) = (Real.sqrt 2) / 2 := by
            have h12 : (2 : ℝ) ^ (- (1 / 2 : ℝ)) = ((2 : ℝ) ^ (1 / 2 : ℝ))⁻¹ := by
              rw [← Real.rpow_neg]
              ring_nf
              all_goals linarith
            have h13 : (2 : ℝ) ^ (1 / 2 : ℝ) = Real.sqrt 2 := by
              rw [← Real.sqrt_eq_rpow]
            rw [h12, h13]
            field_simp
          linarith
        linarith
      have h10 : x ≤ Real.sqrt 2 / 2 := by
        linarith [h9, h8]
      linarith
  · -- Assume x ≤ sqrt 2 / 2, prove abs (logb 2 x) + 1 ≥ 2 + logb 2 x
    intro h
    by_cases h4 : logb 2 x ≥ 0
    · -- Case where logb 2 x ≥ 0
      -- Then from `logb 2 x ≥ 0`, we have x ≥ 1.
      -- But we assumed `x ≤ sqrt 2 / 2` (which is less than 1, since sqrt 2 < 2).
      -- So this is a contradiction.
      have h6 : x ≥ 1 := by
        by_contra h7
        push_neg at h7
        have h8 : logb 2 x < (0 : ℝ) := by
          have h9 : x < (1 : ℝ) := by linarith
          have h10 : logb 2 x < logb 2 1 := by
            apply Real.logb_lt_logb
            all_goals linarith
          have h11 : logb 2 1 = 0 := by
            simp [logb_one]
          nlinarith [h10, h11]
        linarith
      have h7 : x ≤ Real.sqrt 2 / 2 := h
      have h8 : (Real.sqrt 2 / 2 : ℝ) < (1 : ℝ) := by
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by linarith)]
      linarith
    · -- Case where logb 2 x < 0
      have h6 : abs (logb 2 x) = -logb 2 x := by
        rw [abs_of_neg (show logb 2 x < 0 by linarith)]
      rw [h6]
      -- Now the inequality is -logb 2 x + 1 ≥ 2 + logb 2 x
      -- Rearranged: -2 logb 2 x + 1 - 2 ≥ 0, or -2 * logb 2 x -1 ≥ 0
      -- This means logb 2 x ≤ -1/2
      have h7 : logb 2 x ≤ -1 / 2 := by
        have h5 : x ≤ Real.sqrt 2 / 2 := h
        by_contra h7
        push_neg at h7
        have h9 : logb 2 x > -1 / 2 := by linarith
        have h10 : x > (2 : ℝ) ^ (- (1 / 2 : ℝ) ) := by
          have h11 : logb 2 x > -1 / 2 := h9
          have h13 : (2 : ℝ) ^ (logb 2 x : ℝ) = x := by
            field_simp
          have h14 : (2 : ℝ) ^ (- (1 / 2 : ℝ) ) = Real.sqrt 2 / 2 := by
            have h15 : (2 : ℝ) ^ (- (1 / 2 : ℝ) ) = Real.sqrt 2 / 2 := by
              have h16 : (2 : ℝ) ^ (- (1 / 2 : ℝ) ) = (Real.sqrt 2) / 2 := by
                have h17 : (2 : ℝ) ^ (- (1 / 2 : ℝ) ) = ((2 : ℝ) ^ (1 / 2 : ℝ))⁻¹ := by
                  rw [← Real.rpow_neg]
                  ring_nf
                  all_goals linarith
                have h18 : (2 : ℝ) ^ (1 / 2 : ℝ) = Real.sqrt 2 := by
                  rw [← Real.sqrt_eq_rpow]
                rw [h17, h18]
                field_simp
              linarith
            linarith
          have h12 : (2 : ℝ) ^ (logb 2 x : ℝ) > (2 : ℝ) ^ (- (1 / 2 : ℝ) ) := by
            apply Real.rpow_lt_rpow_of_exponent_lt
            all_goals nlinarith
          nlinarith [h13, h12, h14]
        have h11 : (2 : ℝ) ^ (- (1 / 2 : ℝ) ) = Real.sqrt 2 / 2 := by
          have h12 : (2 : ℝ) ^ (- (1 / 2 : ℝ) ) = Real.sqrt 2 / 2 := by
            have h13 : (2 : ℝ) ^ (- (1 / 2 : ℝ) ) = (Real.sqrt 2) / 2 := by
              have h14 : (2 : ℝ) ^ (- (1 / 2 : ℝ) ) = ((2 : ℝ) ^ (1 / 2 : ℝ))⁻¹ := by
                rw [← Real.rpow_neg]
                ring_nf
                all_goals linarith
              have h15 : (2 : ℝ) ^ (1 / 2 : ℝ) = Real.sqrt 2 := by
                rw [← Real.sqrt_eq_rpow]
              rw [h14, h15]
              field_simp
            linarith
          linarith
        nlinarith [h11, h10]
      linarith