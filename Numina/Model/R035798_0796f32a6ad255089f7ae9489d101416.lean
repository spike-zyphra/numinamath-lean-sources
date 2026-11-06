import Mathlib

theorem algebra_609783 :
  {x | x > 0 ∧ x ^ (2 * x ^ 6) = 3} = {(3 : ℝ) ^ ((1 : ℝ) / 6)} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Assume x is a positive real satisfying x^(2x^6)=3, prove x=3^(1/6).
    intro h
    rcases h with ⟨hx1, heq⟩
    have h2 : 2 * x ^ 6 * (Real.log x) = Real.log (3: ℝ) := by
      have h1 : Real.log ((x: ℝ) ^ (2 * x ^ 6)) = Real.log (3: ℝ) := by
        rw [heq]
      have h3 : Real.log ((x: ℝ) ^ (2 * x ^ 6)) = (2 * x ^ 6) * (Real.log x) := by
        rw [Real.log_rpow]
        all_goals nlinarith
      nlinarith
    have h3 : x ^ 6 = (3 : ℝ) := by
      by_cases h4 : x ^ 6 < (3 : ℝ)
      · -- Assume h4
        have h5 : Real.log (x) < (1 / 6) * Real.log (3 : ℝ) := by
          have h10 : x < (3 : ℝ) ^ (1 / 6 : ℝ) := by
            have h4' : x ^ 6 < (3 : ℝ) := h4
            have h12 : ((3 : ℝ) ^ (1 / 6 : ℝ)) ^ 6 = (3 : ℝ) := by
              calc
                ((3 : ℝ) ^ (1 / 6 : ℝ)) ^ 6 = ((3 : ℝ) ^ (1 / 6 : ℝ)) ^ (6 : ℕ) := by rfl
                _ = (3 : ℝ) ^ ((1 / 6 : ℝ) * (6 : ℝ)) := by
                  rw [← Real.rpow_natCast, ← Real.rpow_mul]
                  ring
                  all_goals linarith
                _ = (3 : ℝ) ^ (1: ℝ) := by norm_num
                _ = (3 : ℝ) := by norm_num
            have h12a : x < ((3 : ℝ) ^ (1 / 6 : ℝ)) := by
              by_contra h
              push_neg at h
              have h13a : x ≥ ((3 : ℝ) ^ (1 / 6 : ℝ)) := by linarith
              have h14a : x ^ 6 ≥ ((3 : ℝ) ^ (1 / 6 : ℝ)) ^ 6 := by
                have h15a : x ≥ ((3 : ℝ) ^ (1 / 6 : ℝ)) := h13a
                have h16a : x ^ 6 ≥ ((3 : ℝ) ^ (1 / 6 : ℝ)) ^ 6 := by
                  apply pow_le_pow_left
                  all_goals
                  nlinarith [show 0 ≤ x by linarith, show (0 : ℝ) ≤ (3 : ℝ) ^ (1 / 6 : ℝ) by positivity]
                linarith
              have h17a : ((3 : ℝ) ^ (1 / 6 : ℝ)) ^ 6 = (3: ℝ) := h12
              nlinarith [h4', h17a, h14a]
            linarith
          have h17 : Real.log ((3 : ℝ) ^ (1 / 6 : ℝ)) = (1 / 6 : ℝ) * Real.log (3 : ℝ) := by
            rw [Real.log_rpow]
            all_goals linarith
          have h18 : Real.log x < Real.log ((3 : ℝ) ^ (1 / 6 : ℝ)) := by
            apply Real.log_lt_log
            all_goals
            nlinarith [show 0 < (3 : ℝ) ^ (1 / 6 : ℝ) by positivity, h10]
          nlinarith [h17, h18]
        nlinarith [h2, sq_nonneg (x ^ 3), Real.log_pos (show (3 : ℝ) > 1 by norm_num), Real.log_pos (show (3 : ℝ) > 1 by norm_num)]
      by_cases h5 : x ^ 6 > (3 : ℝ)
      · -- Assume h5
        have h5' : Real.log (x) > (1 / 6) * Real.log (3 : ℝ) := by
          have h10 : x > (3 : ℝ) ^ (1 / 6 : ℝ) := by
            have h4' : x ^ 6 > (3 : ℝ) := h5
            have h12 : ((3 : ℝ) ^ (1 / 6 : ℝ)) ^ 6 = (3 : ℝ) := by
              calc
                ((3 : ℝ) ^ (1 / 6 : ℝ)) ^ 6 = ((3 : ℝ) ^ (1 / 6 : ℝ)) ^ (6 : ℕ) := by rfl
                _ = (3 : ℝ) ^ ((1 / 6 : ℝ) * (6 : ℝ)) := by
                  rw [← Real.rpow_natCast, ← Real.rpow_mul]
                  ring
                  all_goals linarith
                _ = (3 : ℝ) ^ (1: ℝ) := by norm_num
                _ = (3 : ℝ) := by norm_num
            have h12a : x > ((3 : ℝ) ^ (1 / 6 : ℝ)) := by
              by_contra h
              push_neg at h
              have h13a : x ≤ ((3 : ℝ) ^ (1 / 6 : ℝ)) := by linarith
              have h14a : x ^ 6 ≤ ((3 : ℝ) ^ (1 / 6 : ℝ)) ^ 6 := by
                have h15a : x ≤ ((3 : ℝ) ^ (1 / 6 : ℝ)) := h13a
                have h16a : x ^ 6 ≤ ((3 : ℝ) ^ (1 / 6 : ℝ)) ^ 6 := by
                  apply pow_le_pow_left
                  all_goals
                  nlinarith [show 0 ≤ x by linarith, show (0 : ℝ) ≤ (3 : ℝ) ^ (1 / 6 : ℝ) by positivity]
                linarith
              have h17a : ((3 : ℝ) ^ (1 / 6 : ℝ)) ^ 6 = (3: ℝ) := h12
              nlinarith [h4', h17a, h14a]
            linarith
          have h17 : Real.log ((3 : ℝ) ^ (1 / 6 : ℝ)) = (1 / 6 : ℝ) * Real.log (3 : ℝ) := by
            rw [Real.log_rpow]
            all_goals linarith
          have h18 : Real.log x > Real.log ((3 : ℝ) ^ (1 / 6 : ℝ)) := by
            apply Real.log_lt_log
            all_goals
            nlinarith [show 0 < (3 : ℝ) ^ (1 / 6 : ℝ) by positivity, h10]
          nlinarith [h17, h18]
        nlinarith [h2, sq_nonneg (x ^ 3), Real.log_pos (show (3 : ℝ) > 1 by norm_num), Real.log_pos (show (3 : ℝ) > 1 by norm_num)]
      linarith
    have h10 : x = (3: ℝ) ^ ((1: ℝ) / 6) := by
      have h13 : x ^ 6 = (3: ℝ) := h3
      have h14 : x > 0 := hx1
      have h15 : x = ((x) ^ 6) ^ (1 / 6 : ℝ) := by
        have h16a : ((x) ^ 6) ^ (1 / 6: ℝ) = (x: ℝ) := by
          have h17a1 : x ^ 6 = (x) ^ 6 := by ring
          have h18a1 : ((x) ^ 6) ^ (1 / 6: ℝ) = (x: ℝ) := by
            rw [h17a1]
            rw [← Real.rpow_natCast, ← Real.rpow_mul]
            norm_num
            all_goals linarith [show 0 ≤ x by linarith]
          linarith
        linarith
      rw [show (x ^ 6 : ℝ) = (3: ℝ) by linarith] at h15
      nlinarith
    linarith [h10]
  · -- Assume x=3^(1/6), prove x>0 and equation.
    intro heq
    rw [heq]
    constructor
    · -- Show 3^(1/6)>0
      positivity
    · -- Show 3^ (1/6)^(2*(3^ (1/6))^6)=3
      have h1 : ((3 : ℝ) ^ ((1 : ℝ) / 6)) ^ 6 = (3 : ℝ) := by
        calc
          ((3 : ℝ) ^ ((1 : ℝ) / 6)) ^ 6 = ((3 : ℝ) ^ ((1 : ℝ) / 6)) ^ (6: ℕ) := by rfl
          _ = (3) ^ ((1: ℝ) / 6 * (6: ℝ)) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul]
            ring
            all_goals norm_num
          _ = (3: ℝ) := by
            norm_num
      have h4 : (2 * ((3 : ℝ) ^ ((1 : ℝ) / 6)) ^ 6) = (6: ℝ) := by
        nlinarith [h1]
      have h5 : ((3 : ℝ) ^ ((1 : ℝ) / 6)) ^ (2 * ((3 : ℝ) ^ ((1 : ℝ) / 6)) ^ 6) = (3: ℝ) := by
        rw [h4]
        have h6 : ((3 : ℝ) ^ ((1 : ℝ) / 6)) ^ (6: ℝ) = (3: ℝ) := by
          calc
            ((3 : ℝ) ^ ((1 : ℝ) / 6)) ^ (6: ℝ) = (3: ℝ) ^ (( (1 : ℝ) / 6 ) * (6: ℝ) ) := by
              rw [← Real.rpow_mul]
              ring
              all_goals linarith
            _ = (3: ℝ) := by
              norm_num
        exact h6
      exact h5