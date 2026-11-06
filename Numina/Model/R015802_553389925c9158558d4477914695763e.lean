import Mathlib

theorem algebra_224093 : ((5 * Real.sqrt 2 + 7) ^ ((1 : ℝ) / 3) - (5 * Real.sqrt 2 - 7) ^ ((1 : ℝ) / 3)) = 2 := by
  have h1 : Real.sqrt 2 > 0 := by
    apply Real.sqrt_pos.mpr
    all_goals norm_num

  have h2 : (5 * Real.sqrt 2) ^ 2 = 50 := by
    calc
      (5 * Real.sqrt 2) ^ 2 = 5 ^ 2 * (Real.sqrt 2) ^ 2 := by ring
      _ = 25 * 2 := by norm_num [Real.sq_sqrt]
      _ = 50 := by norm_num

  have h3 : (5 * Real.sqrt 2 + 7) * (5 * Real.sqrt 2 - 7) = 1 := by
    nlinarith [h2, Real.sqrt_nonneg 2]

  have h4 : ((5 * Real.sqrt 2 + 7) ^ ((1 : ℝ) / 3)) * ((5 * Real.sqrt 2 - 7) ^ ((1 : ℝ) / 3)) = 1 := by
    have h5 : ((5 * Real.sqrt 2 + 7) ^ ((1 : ℝ) / 3)) * ((5 * Real.sqrt 2 - 7) ^ ((1 : ℝ) / 3)) = ((5 * Real.sqrt 2 + 7) * (5 * Real.sqrt 2 - 7)) ^ ((1 : ℝ) / 3) := by
      rw [← Real.mul_rpow]
      all_goals
        nlinarith [show 0 ≤ (5 * Real.sqrt 2 - 7 : ℝ) by nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), sq_nonneg (Real.sqrt 2 - 7 / 5)]]
    rw [h5]
    rw [h3]
    norm_num

  have h5 : ((5 * Real.sqrt 2 + 7) ^ ((1 : ℝ) / 3) - (5 * Real.sqrt 2 - 7) ^ ((1 : ℝ) / 3)) ^ 3 + 3 * ((5 * Real.sqrt 2 + 7) ^ ((1 : ℝ) / 3) - (5 * Real.sqrt 2 - 7) ^ ((1 : ℝ) / 3)) - 14 = 0 := by
    have h6 : ((5 * Real.sqrt 2 + 7) ^ ((1 : ℝ) / 3)) ^ 3 = 5 * Real.sqrt 2 + 7 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul]
      norm_num
      all_goals
        nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    have h7 : ((5 * Real.sqrt 2 - 7) ^ ((1 : ℝ) / 3)) ^ 3 = 5 * Real.sqrt 2 - 7 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul]
      norm_num
      all_goals
        nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), sq_nonneg (Real.sqrt 2 - 7 / 5)]
    have h8 : ((5 * Real.sqrt 2 + 7) ^ ((1 : ℝ) / 3) - (5 * Real.sqrt 2 - 7) ^ ((1 : ℝ) / 3)) ^ 3 = ((5 * Real.sqrt 2 + 7) ^ ((1 : ℝ) / 3)) ^ 3 - ((5 * Real.sqrt 2 - 7) ^ ((1 : ℝ) / 3)) ^ 3 - 3 * (( (5 * Real.sqrt 2 + 7) ^ ((1 : ℝ) / 3) ) * ((5 * Real.sqrt 2 - 7) ^ ((1 : ℝ) / 3)) ) * (( (5 * Real.sqrt 2 + 7) ^ ((1 : ℝ) / 3) - (5 * Real.sqrt 2 - 7) ^ ((1 : ℝ) / 3) )) := by
      ring
    rw [h8, h6, h7, h4]
    nlinarith

  have h7 : ((5 * Real.sqrt 2 + 7) ^ ((1 : ℝ) / 3) - (5 * Real.sqrt 2 - 7) ^ ((1 : ℝ) / 3)) = 2 := by
    have h8 : ((5 * Real.sqrt 2 + 7) ^ ((1 : ℝ) / 3) - (5 * Real.sqrt 2 - 7) ^ ((1 : ℝ) / 3) - 2) * (((5 * Real.sqrt 2 + 7) ^ ((1 : ℝ) / 3) - (5 * Real.sqrt 2 - 7) ^ ((1 : ℝ) / 3)) ^ 2 + 2 * ((5 * Real.sqrt 2 + 7) ^ ((1 : ℝ) / 3) - (5 * Real.sqrt 2 - 7) ^ ((1 : ℝ) / 3)) + 7) = 0 := by
      nlinarith [h5]
    cases' (mul_eq_zero.mp h8) with h9 h10
    ·
      linarith
    ·
      nlinarith [sq_nonneg ((5 * Real.sqrt 2 + 7) ^ ((1 : ℝ) / 3) - (5 * Real.sqrt 2 - 7) ^ ((1 : ℝ) / 3) + 1), Real.sqrt_nonneg 2]

  exact h7