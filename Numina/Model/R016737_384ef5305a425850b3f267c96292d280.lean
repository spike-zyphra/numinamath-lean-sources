import Mathlib

theorem algebra_83835 : ∃ q : ℚ, (Real.sqrt 52 + 5) ^ ((1 : ℝ) / 3) - (Real.sqrt 52 - 5) ^ ((1 : ℝ) / 3) = q := by
  refine' ⟨(1 : ℚ), by
    have h1 : Real.sqrt 52 ≥ 0 := by positivity
    have h52sqrt : 0 ≤ Real.sqrt 52 - 5 := by
      have h1 : 52 ≥ (25 : ℝ) := by norm_num
      have h2 : Real.sqrt 52 ≥ Real.sqrt 25 := Real.sqrt_le_sqrt (by linarith)
      have h3 : Real.sqrt (25 : ℝ) = (5 : ℝ) := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      have h4 : Real.sqrt 52 ≥ (5 : ℝ) := by linarith [h2, h3]
      linarith
    have h52_cubed : ((Real.sqrt 52 + 5) ^ ((1 : ℝ) / 3)) ^ 3 = Real.sqrt 52 + 5 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul]
      norm_num
      all_goals linarith [Real.sqrt_nonneg 52]
    have h0385_cubed : ((Real.sqrt 52 - 5) ^ ((1 : ℝ) / 3)) ^ 3 = Real.sqrt 52 - 5 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul]
      norm_num
      all_goals nlinarith [Real.sqrt_nonneg 52, h52sqrt]
    have h6 : ((Real.sqrt 52 + 5) ^ ((1 : ℝ) / 3) - (Real.sqrt 52 - 5) ^ ((1 : ℝ) / 3)) ^ 3 = 10 - 9 * ((Real.sqrt 52 + 5) ^ ((1 : ℝ) / 3) - (Real.sqrt 52 - 5) ^ ((1 : ℝ) / 3)) := by
      have h8 : ((Real.sqrt 52 + 5) ^ ((1 : ℝ) / 3) - (Real.sqrt 52 - 5) ^ ((1 : ℝ) / 3)) ^ 3 = ((Real.sqrt 52 + 5) ^ ((1 : ℝ) / 3)) ^ 3 - ((Real.sqrt 52 - 5) ^ ((1 : ℝ) / 3)) ^ 3 - 3 * ((Real.sqrt 52 + 5) ^ ((1 : ℝ) / 3) * ((Real.sqrt 52 - 5) ^ ((1 : ℝ) / 3))) * ((Real.sqrt 52 + 5) ^ ((1 : ℝ) / 3) - (Real.sqrt 52 - 5) ^ ((1 : ℝ) / 3)) := by ring
      have h9 : ((Real.sqrt 52 + 5) ^ ((1 : ℝ) / 3)) ^ 3 - ((Real.sqrt 52 - 5) ^ ((1 : ℝ) / 3)) ^ 3 = 10 := by
        rw [h52_cubed, h0385_cubed]
        nlinarith [Real.sqrt_nonneg 52, Real.sq_sqrt (show 0 ≤ (52 : ℝ) by norm_num), sq_nonneg (Real.sqrt 52 * Real.sqrt 52), h52sqrt, h1]
      have h10 : ((Real.sqrt 52 + 5) ^ ((1 : ℝ) / 3) * ((Real.sqrt 52 - 5) ^ ((1 : ℝ) / 3))) = (3 : ℝ) := by
        have h91 : ((Real.sqrt 52 + 5) ^ ((1 : ℝ) / 3) * ((Real.sqrt 52 - 5) ^ ((1 : ℝ) / 3))) = (((Real.sqrt 52 + 5 : ℝ) * (Real.sqrt 52 - 5 : ℝ)) ^ ((1 : ℝ) / 3)) := by
          rw [← Real.mul_rpow]
          all_goals nlinarith [Real.sqrt_nonneg 52, h52sqrt]
        have h92 : (Real.sqrt 52 + 5 : ℝ) * (Real.sqrt 52 - 5 : ℝ) = (27 : ℝ) := by
          nlinarith [Real.sqrt_nonneg 52, Real.sq_sqrt (show 0 ≤ (52 : ℝ) by norm_num)]
        rw [h91, h92]
        have h82 : (27 : ℝ) ^ ((1 : ℝ) / 3) = (3 : ℝ) := by
          rw [show (27 : ℝ) = 3 ^ (3 : ℝ) by norm_num]
          rw [← Real.rpow_mul]
          norm_num
          all_goals norm_num
          all_goals linarith
        rw [h82]
        all_goals norm_num
        all_goals nlinarith
      -- Combine previous results
      nlinarith [h8, h9, h10, sq_nonneg ((Real.sqrt 52 + 5 : ℝ) ^ ((1 : ℝ) / 3) - (Real.sqrt 52 - 5 : ℝ) ^ ((1 : ℝ) / 3)), sq_nonneg ((Real.sqrt 52 + 5 : ℝ) ^ ((1 : ℝ) / 3) + (Real.sqrt 52 - 5 : ℝ) ^ ((1 : ℝ) / 3) - 1), sq_nonneg ((Real.sqrt 52 + 5 : ℝ) ^ ((1 : ℝ) / 3) - (Real.sqrt 52 - 5 : ℝ) ^ ((1 : ℝ) / 3) * 1), sq_nonneg ((Real.sqrt 52 + 5 : ℝ) ^ ((1 : ℝ) / 3) * ((Real.sqrt 52 - 5 : ℝ) ^ ((1 : ℝ) / 3)) * 1)]
    have h7 : ((Real.sqrt 52 + 5) ^ ((1 : ℝ) / 3) - (Real.sqrt 52 - 5) ^ ((1 : ℝ) / 3) - (1 : ℝ)) * (((Real.sqrt 52 + 5) ^ ((1 : ℝ) / 3) - (Real.sqrt 52 - 5) ^ ((1 : ℝ) / 3)) ^ 2 + ((Real.sqrt 52 + 5) ^ ((1 : ℝ) / 3) - (Real.sqrt 52 - 5) ^ ((1 : ℝ) / 3)) + (1 : ℝ)) = 0 := by
      nlinarith [sq_nonneg ((Real.sqrt 52 + 5 : ℝ) ^ ((1 : ℝ) / 3) - (Real.sqrt 52 - 5 : ℝ) ^ ((1 : ℝ) / 3) - (1 : ℝ)), sq_nonneg ((Real.sqrt 52 + 5 : ℝ) ^ ((1 : ℝ) / 3) - (Real.sqrt 52 - 5 : ℝ) ^ ((1 : ℝ) / 3)), sq_nonneg ((Real.sqrt 52 + 5 : ℝ) ^ ((1 : ℝ) / 3) * ((Real.sqrt 52 - 5 : ℝ) ^ ((1 : ℝ) / 3)) * 1), sq_nonneg ((Real.sqrt 52 + 5 : ℝ) ^ ((1 : ℝ) / 3) * ((Real.sqrt 52 - 5 : ℝ) ^ ((1 : ℝ) / 3)) * ((Real.sqrt 52 + 5 : ℝ) ^ ((1 : ℝ) / 3) - (Real.sqrt 52 - 5 : ℝ) ^ ((1 : ℝ) / 3))), Real.sqrt_nonneg 52, Real.sq_sqrt (show 0 ≤ (52 : ℝ) by norm_num), sq_nonneg ((Real.sqrt 52 + 5 : ℝ) ^ ((1 : ℝ) / 3) - (Real.sqrt 52 - 5 : ℝ) ^ ((1 : ℝ) / 3) * 1)]
    cases' (mul_eq_zero.mp h7) with h8 h9
    · -- Case difference - 1 = 0
      linarith
    · -- Case quadratic factor = 0
      nlinarith [sq_nonneg ((Real.sqrt 52 + 5 : ℝ) ^ ((1 : ℝ) / 3) - (Real.sqrt 52 - 5 : ℝ) ^ ((1 : ℝ) / 3)), sq_nonneg ((Real.sqrt 52 + 5 : ℝ) ^ ((1 : ℝ) / 3) + (Real.sqrt 52 - 5 : ℝ) ^ ((1 : ℝ) / 3) - 1), Real.sqrt_nonneg 52, Real.sq_sqrt (show 0 ≤ (52 : ℝ) by norm_num)]
  ⟩