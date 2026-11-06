import Mathlib

/-Solve the equation 3 ^2x * 5^ (3x-4) = 7^(x-1) * 11^ (2-x)-/
theorem algebra_6431 (x : ℝ) : (3 : ℝ)^(2 * x) * (5 : ℝ)^(3 * x - 4) =
    (7 : ℝ)^(x - 1) * (11 : ℝ)^(2 - x) ↔
    x = (2 * Real.log 11 - Real.log 7 + 4 * Real.log 5) / (2 * Real.log 3 + 3 * Real.log 5 - Real.log 7 + Real.log 11) := by
  constructor
  · -- Assume (3 : ℝ)^(2 * x) * (5 : ℝ)^(3 * x - 4) = (7 : ℝ)^(x - 1) * (11 : ℝ)^(2 - x) --
    --we need to prove x = (2 * Real.log 11 - Real.log 7 + 4 * Real.log 5) / (2 * Real.log 3 + 3 * Real.log 5 - Real.log 7 + Real.log 11) --
    intro h
    -- firstly, we just use log to simplify the equation step by step --
    have h1 : Real.log ((3 : ℝ)^(2 * x) * (5 : ℝ)^(3 * x - 4)) = Real.log ((7 : ℝ)^(x - 1) * (11 : ℝ)^(2 - x)) := by
      rw [h]
    have h2 : Real.log ((3 : ℝ)^(2 * x) * (5 : ℝ)^(3 * x - 4)) = Real.log ((3 : ℝ)^(2 * x)) + Real.log ((5 : ℝ)^(3 * x - 4)) := by
      rw [Real.log_mul (by positivity) (by positivity)]
    have h3 : Real.log ((7 : ℝ)^(x - 1) * (11 : ℝ)^(2 - x)) = Real.log ((7 : ℝ)^(x - 1)) + Real.log ((11 : ℝ)^(2 - x)) := by
      rw [Real.log_mul (by positivity) (by positivity)]
    have h4 : Real.log ((3 : ℝ)^(2 * x)) = 2 * x * Real.log 3 := by
      simp [Real.log_rpow]
    have h5 : Real.log ((5 : ℝ)^(3 * x - 4)) = (3 * x - 4) * Real.log 5 := by
      simp [Real.log_rpow]
    have h6 : Real.log ((7 : ℝ)^(x - 1)) = (x - 1) * Real.log 7 := by
      simp [Real.log_rpow]
    have h7 : Real.log ((11 : ℝ)^(2 - x)) = (2 - x) * Real.log 11 := by
      simp [Real.log_rpow]
    -- plug them to simplify the equation --
    rw [h2, h4, h5, h3, h6, h7] at h1
    -- to divide the equation, we need to make sure the denominator is not zero --
    have h8 : (2 * Real.log 3 + 3 * Real.log 5 - Real.log 7 + Real.log 11) ≠ 0 := by
      by_contra h9
      have h10 : (3 : ℝ) ^ (2 : ℝ) * (5 : ℝ) ^ (3 : ℝ) * (11 : ℝ) = (7 : ℝ) := by
        have h11 : (3 : ℝ) ^ (2 : ℝ) * (5 : ℝ) ^ (3 : ℝ) * (11 : ℝ) = Real.exp (Real.log ((3 : ℝ) ^ (2 : ℝ) * (5 : ℝ) ^ (3 : ℝ) * (11 : ℝ))) := by
          rw [Real.exp_log]
          all_goals linarith [Real.rpow_pos_of_pos (show (0:ℝ) < 3 by norm_num) 2, Real.rpow_pos_of_pos (show (0:ℝ) < 5 by norm_num) 3, show (0:ℝ) < 11 by norm_num]
        have h12 : Real.log ((3 : ℝ) ^ (2 : ℝ) * (5 : ℝ) ^ (3 : ℝ) * (11 : ℝ)) = Real.log (7 : ℝ) := by
          have h13 : Real.log ((3 : ℝ) ^ (2 : ℝ) * (5 : ℝ) ^ (3 : ℝ) * (11 : ℝ)) = 2 * Real.log 3 + 3 * Real.log 5 + Real.log 11 := by
            simp [Real.log_mul, Real.log_rpow]
          linarith [h9, h13]
        rw [h11, h12]
        all_goals linarith [Real.exp_log (show 0 < (7 : ℝ)  by norm_num)]
      norm_num at h10
    have h9 : (2 * Real.log 3 + 3 * Real.log 5 - Real.log 7 + Real.log 11) * x = 2 * Real.log 11 - Real.log 7 + 4 * Real.log 5 := by
      linarith
    have h10 : x = (2 * Real.log 11 - Real.log 7 + 4 * Real.log 5) / (2 * Real.log 3 + 3 * Real.log 5 - Real.log 7 + Real.log 11) := by
      field_simp [h8]
      linarith
    exact h10
  · -- Now prove the reverse direction, it's similar to the first part, just reverse the proof --
    intro h
    have h1 : (3 : ℝ)^(2 * x) * (5 : ℝ)^(3 * x - 4) = (7 : ℝ)^(x - 1) * (11 : ℝ)^(2 - x) := by
      have h2 : (2 * Real.log 3 + 3 * Real.log 5 - Real.log 7 + Real.log 11) ≠ 0 := by
        by_contra h3
        have h4 : (3 : ℝ) ^ (2 : ℝ) * (5 : ℝ) ^ (3 : ℝ) * (11 : ℝ) = (7 : ℝ) := by
          have h5 : (3 : ℝ) ^ (2 : ℝ) * (5 : ℝ) ^ (3 : ℝ) * (11 : ℝ) = Real.exp (Real.log ((3 : ℝ) ^ (2 : ℝ) * (5 : ℝ) ^ (3 : ℝ) * (11 : ℝ))) := by
            rw [Real.exp_log]
            all_goals linarith [Real.rpow_pos_of_pos (show (0:ℝ) < 3 by norm_num) 2, Real.rpow_pos_of_pos (show (0:ℝ) < 5 by norm_num) 3, show (0:ℝ) < 11 by norm_num]
          have h6 : Real.log ((3 : ℝ) ^ (2 : ℝ) * (5 : ℝ) ^ (3 : ℝ) * (11 : ℝ)) = Real.log (7 : ℝ) := by
            have h7 : Real.log ((3 : ℝ) ^ (2 : ℝ) * (5 : ℝ) ^ (3 : ℝ) * (11 : ℝ)) = 2 * Real.log 3 + 3 * Real.log 5 + Real.log 11 := by
              simp [Real.log_mul, Real.log_rpow]
            linarith [h3, h7]
          rw [h5, h6]
          all_goals linarith [Real.exp_log (show 0 < (7 : ℝ)  by norm_num)]
        norm_num at h4
       -- similarly, we show some results step by step --
      have h3 : Real.log ((3 : ℝ) ^ (2 * x) * (5 : ℝ) ^ (3 * x - 4)) = Real.log ((7 : ℝ) ^ (x - 1) * (11 : ℝ) ^ (2 - x)) := by
        have h4 : Real.log ((3 : ℝ) ^ (2 * x) * (5 : ℝ) ^ (3 * x - 4)) = Real.log ((3 : ℝ) ^ (2 * x)) + Real.log ((5 : ℝ) ^ (3 * x - 4)) := by
          rw [Real.log_mul (by positivity) (by positivity)]
        have h5 : Real.log ((7 : ℝ) ^ (x - 1) * (11 : ℝ) ^ (2 - x)) = Real.log ((7 : ℝ) ^ (x - 1)) + Real.log ((11 : ℝ) ^ (2 - x)) := by
          rw [Real.log_mul (by positivity) (by positivity)]
        have h6 : Real.log ((3 : ℝ) ^ (2 * x)) = 2 * x * Real.log 3 := by
          simp [Real.log_rpow]
        have h7 : Real.log ((5 : ℝ) ^ (3 * x - 4)) = (3 * x - 4) * Real.log 5 := by
          simp [Real.log_rpow]
        have h8 : Real.log ((7 : ℝ) ^ (x - 1)) = (x - 1) * Real.log 7 := by
          simp [Real.log_rpow]
        have h9 : Real.log ((11 : ℝ) ^ (2 - x)) = (2 - x) * Real.log 11 := by
          simp [Real.log_rpow]
        rw [h4, h6, h7, h5, h8, h9]
        have h10 : (2 * Real.log 3 + 3 * Real.log 5 - Real.log 7 + Real.log 11) * x = 2 * Real.log 11 - Real.log 7 + 4 * Real.log 5 := by
          field_simp [h2] at h ⊢
          linarith
        linarith [h10]
      have h7 : (3 : ℝ) ^ (2 * x) * (5 : ℝ) ^ (3 * x - 4) = Real.exp (Real.log ((3 : ℝ) ^ (2 * x) * (5 : ℝ) ^ (3 * x - 4))) := by
        rw [Real.exp_log]
        all_goals positivity
      have h8 : (7 : ℝ) ^ (x - 1) * (11 : ℝ) ^ (2 - x) = Real.exp (Real.log ((7 : ℝ) ^ (x - 1) * (11 : ℝ) ^ (2 - x))) := by
        rw [Real.exp_log]
        all_goals positivity
      -- finally, we can plug them to get the result --
      rw [h7, h8, h3]
    exact h1
    