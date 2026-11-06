import Mathlib

open Real

theorem algebra_194349 {z : ℝ} (hz : z = (1620 + 12 * sqrt 17457) ^ ((1 : ℝ) / 3) +
    (1620 - 12 * sqrt 17457) ^ ((1 : ℝ) / 3)) : z = 18 := by

  have h1 : z = (1620 + 12 * sqrt 17457) ^ ((1 : ℝ) / 3) + (1620 - 12 * sqrt 17457) ^ ((1 : ℝ) / 3) := by
    linarith [hz]

  have h2 : z^3 = 3240 + 144 * z := by
    rw [h1]
    have h3 : ((1620 + 12 * sqrt 17457 : ℝ) ^ ((1 : ℝ) / 3) + (1620 - 12 * sqrt 17457 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 =
        ((1620 + 12 * sqrt 17457 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 + ((1620 - 12 * sqrt 17457 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 + 3 * ((1620 + 12 * sqrt 17457 : ℝ) ^ ((1 : ℝ) / 3) * ((1620 - 12 * sqrt 17457 : ℝ) ^ ((1 : ℝ) / 3)) ) * ((1620 + 12 * sqrt 17457 : ℝ) ^ ((1 : ℝ) / 3) + (1620 - 12 * sqrt 17457 : ℝ) ^ ((1 : ℝ) / 3)) := by
      ring

    have h4 : ((1620 + 12 * sqrt 17457 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = (1620 + 12 * sqrt 17457 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul]
      norm_num
      all_goals
        nlinarith [Real.sqrt_nonneg 17457]

    have h5 : ((1620 - 12 * sqrt 17457 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = (1620 - 12 * sqrt 17457 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul]
      norm_num
      all_goals
        nlinarith [Real.sqrt_nonneg 17457, Real.sq_sqrt (show (0 : ℝ) ≤ 17457 by norm_num)]

    have h6 : ( (1620 + 12 * sqrt 17457 : ℝ) ^ ((1 : ℝ) / 3) ) * ( (1620 - 12 * sqrt 17457 : ℝ) ^ ((1 : ℝ) / 3) ) = (48 : ℝ) := by
      have h7 : ( (1620 + 12 * sqrt 17457 : ℝ) ^ ((1 : ℝ) / 3) ) * ( (1620 - 12 * sqrt 17457 : ℝ) ^ ((1 : ℝ) / 3) ) =
          ( (1620 + 12 * sqrt 17457) * (1620 - 12 * sqrt 17457) ) ^ ((1 : ℝ) / 3) := by
        rw [← Real.mul_rpow]
        all_goals
          nlinarith [Real.sqrt_nonneg 17457, Real.sq_sqrt (show (0 : ℝ) ≤ 17457 by norm_num)]

      rw [h7]
      have h8 : ( (1620 + 12 * sqrt 17457) * (1620 - 12 * sqrt 17457) ) = (110592 : ℝ) := by
        nlinarith [Real.sqrt_nonneg 17457, Real.sq_sqrt (show (0 : ℝ) ≤ 17457 by norm_num)]

      rw [h8]
      have h9 : ( (110592 : ℝ) ^ ((1 : ℝ) / 3) ) = (48 : ℝ) := by
        have h10 : ( (110592 : ℝ) ^ ((1 : ℝ) / 3) ) = (48 : ℝ) := by
          rw [show (110592 : ℝ) = (48 : ℝ) ^ (3 : ℝ) by norm_num]
          rw [← Real.rpow_mul]
          norm_num
          all_goals
            norm_num
        linarith
      linarith

    rw [h3, h4, h5, h6]
    all_goals
      ring

  have h3 : (z - 18) * (z^2 + 18 * z + 180) = 0 := by
    nlinarith [h2, sq_nonneg (z - 18), sq_nonneg (z + 9)]

  cases' (mul_eq_zero.mp h3) with h4 h5
  · -- Case z - 18 = 0
    linarith

  · -- Case z^2 + 18 * z + 180 = 0
    nlinarith [sq_nonneg (z + 9)]