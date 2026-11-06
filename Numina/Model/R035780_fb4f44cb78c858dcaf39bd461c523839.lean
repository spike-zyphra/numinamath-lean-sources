import Mathlib

theorem algebra_143927 : (26 + 15 * Real.sqrt 3) ^ ((1 : ℝ) / 3) + (26 - 15 * Real.sqrt 3) ^ ((1 : ℝ) / 3) = 4 := by
  have h1 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have h2 : Real.sqrt 3 ^ 4 = 9 := by
    calc
      (Real.sqrt 3) ^ 4 = ((Real.sqrt 3) ^ 2) ^ 2 := by ring
      _ = 3 ^ 2 := by rw [h1]
      _ = 9 := by norm_num
  have h3 : (26 + 15 * Real.sqrt 3) * (26 - 15 * Real.sqrt 3) = 1 := by
    nlinarith [h1, sq_nonneg (Real.sqrt 3)]
  have h4 : ((26 + 15 * Real.sqrt 3) ^ ((1 : ℝ) / 3)) * ((26 - 15 * Real.sqrt 3) ^ ((1 : ℝ) / 3)) = 1 := by
    have h5 : ((26 + 15 * Real.sqrt 3) ^ ((1 : ℝ) / 3)) * ((26 - 15 * Real.sqrt 3) ^ ((1 : ℝ) / 3)) =
      ((26 + 15 * Real.sqrt 3) * (26 - 15 * Real.sqrt 3)) ^ ((1 : ℝ) / 3) := by
      rw [← Real.mul_rpow]
      all_goals
        nlinarith [Real.sqrt_nonneg 3, Real.sqrt_pos.mpr (show (3 : ℝ) > 0 by norm_num)]
    rw [h5, h3]
    norm_num [Real.rpow_natCast, Real.rpow_zero, Real.rpow_pos_of_pos]
    all_goals nlinarith
  -- We need to show now that s^3 = 4s + 52 a real s only root is 4.
  have h5 : ((26 + 15 * Real.sqrt 3) ^ ((1 : ℝ) / 3) + (26 - 15 * Real.sqrt 3) ^ ((1 : ℝ) / 3)) ^ 3 = 52 + 3 * ((26 + 15 * Real.sqrt 3) ^ ((1 : ℝ) / 3) + (26 - 15 * Real.sqrt 3) ^ ((1 : ℝ) / 3)) := by
    have h6 : ((26 + 15 * Real.sqrt 3) ^ ((1 : ℝ) / 3) + (26 - 15 * Real.sqrt 3) ^ ((1 : ℝ) / 3)) ^ 3 =
        ((26 + 15 * Real.sqrt 3) ^ ((1 : ℝ) / 3)) ^ 3 + ((26 - 15 * Real.sqrt 3) ^ ((1 : ℝ) / 3)) ^ 3 + 3 * ((26 + 15 * Real.sqrt 3) ^ ((1 : ℝ) / 3) * ((26 - 15 * Real.sqrt 3) ^ ((1 : ℝ) / 3))) * ((26 + 15 * Real.sqrt 3) ^ ((1 : ℝ) / 3) + (26 - 15 * Real.sqrt 3) ^ ((1 : ℝ) / 3)) := by
      ring
    have h7 : ((26 + 15 * Real.sqrt 3) ^ ((1 : ℝ) / 3)) ^ 3 = 26 + 15 * Real.sqrt 3 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul]
      norm_num
      all_goals nlinarith [Real.sqrt_nonneg 3, Real.sqrt_pos.mpr (show (3 : ℝ) > 0 by norm_num)]
    have h8 : ((26 - 15 * Real.sqrt 3) ^ ((1 : ℝ) / 3)) ^ 3 = 26 - 15 * Real.sqrt 3 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul]
      norm_num
      all_goals nlinarith [Real.sqrt_nonneg 3, Real.sqrt_pos.mpr (show (3 : ℝ) > 0 by norm_num), sq_nonneg (Real.sqrt 3 ^ 2 - 3)]
    rw [h6, h7, h8, h4]
    nlinarith
  have h6 : ((26 + 15 * Real.sqrt 3) ^ ((1 : ℝ) / 3) + (26 - 15 * Real.sqrt 3) ^ ((1 : ℝ) / 3) - 4) * ((26 + 15 * Real.sqrt 3) ^ ((1 : ℝ) / 3) + (26 - 15 * Real.sqrt 3) ^ ((1 : ℝ) / 3) + 4) = 0 := by
    have h7 : ((26 + 15 * Real.sqrt 3) ^ ((1 : ℝ) / 3) + (26 - 15 * Real.sqrt 3) ^ ((1 : ℝ) / 3)) ^ 3 = 52 + 3 * ((26 + 15 * Real.sqrt 3) ^ ((1 : ℝ) / 3) + (26 - 15 * Real.sqrt 3) ^ ((1 : ℝ) / 3)) := h5
    nlinarith [sq_nonneg ((26 + 15 * Real.sqrt 3) ^ ((1 : ℝ) / 3) + (26 - 15 * Real.sqrt 3) ^ ((1 : ℝ) / 3) - 4), sq_nonneg ((26 + 15 * Real.sqrt 3) ^ ((1 : ℝ) / 3) + (26 - 15 * Real.sqrt 3) ^ ((1 : ℝ) / 3) + 4), Real.sqrt_pos.mpr (show (3 : ℝ) > 0 by norm_num)]
  cases' (mul_eq_zero.mp h6) with h7 h8
  · -- Case s - 4 = 0
    linarith
  · -- Show s + 4 ≠ 0
    have h7 : ((26 + 15 * Real.sqrt 3) ^ ((1 : ℝ) / 3) + (26 - 15 * Real.sqrt 3) ^ ((1 : ℝ) / 3)) ^ 2 + 4 * ((26 + 15 * Real.sqrt 3) ^ ((1 : ℝ) / 3) + (26 - 15 * Real.sqrt 3) ^ ((1 : ℝ) / 3)) + 13 > 0 := by
      nlinarith [sq_nonneg ((26 + 15 * Real.sqrt 3) ^ ((1 : ℝ) / 3) + (26 - 15 * Real.sqrt 3) ^ ((1 : ℝ) / 3)), sq_nonneg ((26 + 15 * Real.sqrt 3) ^ ((1 : ℝ) / 3) - (26 - 15 * Real.sqrt 3) ^ ((1 : ℝ) / 3)), Real.sqrt_nonneg 3, sq_nonneg (Real.sqrt 3 ^ 2 - 3)]
    nlinarith [sq_nonneg ((26 + 15 * Real.sqrt 3) ^ ((1 : ℝ) / 3) + (26 - 15 * Real.sqrt 3) ^ ((1 : ℝ) / 3) + 4), h7, Real.sqrt_pos.mpr (show (3 : ℝ) > 0 by norm_num)]