import Mathlib

open Real

theorem algebra_4719 : ((9 + 4 * sqrt 5) ^ ((3 : ℝ) / 2) +
    (9 - 4 * sqrt 5) ^ ((3 : ℝ) / 2)) /
    ((11 + 2 * sqrt 30) ^ ((3 : ℝ) / 2) -
    (11 - 2 * sqrt 30) ^ ((3 : ℝ) / 2)) = 17 / 23 := by

  have h1 : (9 + 4 * sqrt 5) = (sqrt 5 + 2) ^ 2 := by
    nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]

  have h2 : (9 - 4 * sqrt 5) = (sqrt 5 - 2) ^ 2 := by
    nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]

  have h3 : (11 + 2 * sqrt 30) = (sqrt 6 + sqrt 5) ^ 2 := by
    have h4 : sqrt 30 = sqrt 6 * sqrt 5 := by
      rw [show (30 : ℝ) = 6 * 5 by norm_num]
      field_simp [Real.sqrt_mul]
    nlinarith [Real.sqrt_nonneg 6, Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), h4]

  have h5 : (11 - 2 * sqrt 30) = (sqrt 6 - sqrt 5) ^ 2 := by
    have h6 : sqrt 30 = sqrt 6 * sqrt 5 := by
      rw [show (30 : ℝ) = 6 * 5 by norm_num]
      field_simp [Real.sqrt_mul]
    nlinarith [Real.sqrt_nonneg 6, Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), h6]

  have h7 : (9 + 4 * sqrt 5 : ℝ) ^ ((3 : ℝ) / 2) = (sqrt 5 + 2) ^ 3 := by
    have h8 : (9 + 4 * sqrt 5 : ℝ) ^ ((3 : ℝ) / 2) = ((sqrt 5 + 2) ^ 2) ^ ((3 : ℝ) / 2) := by
      rw [h1]
    have h9 : ((sqrt 5 + 2 : ℝ) ^ 2) ^ ((3 : ℝ) / 2) = (sqrt 5 + 2 : ℝ) ^ (3 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul]
      norm_num
      all_goals nlinarith [Real.sqrt_nonneg 5, show sqrt 5 + 2 > 0 by positivity]
    rw [h8, h9]
    norm_cast

  have h7' : (9 - 4 * sqrt 5 : ℝ) ^ ((3 : ℝ) / 2) = (sqrt 5 - 2) ^ 3 := by
    have h8 : (9 - 4 * sqrt 5 : ℝ) ^ ((3 : ℝ) / 2) = ((sqrt 5 - 2) ^ 2) ^ ((3 : ℝ) / 2) := by
      rw [h2]
    have h9 : ((sqrt 5 - 2 : ℝ) ^ 2) ^ ((3 : ℝ) / 2) = (sqrt 5 - 2 : ℝ) ^ (3 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul]
      norm_num
      all_goals
        have h7 : sqrt 5 > 2 := by
          nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), Real.sqrt_nonneg (5 : ℝ)]
        have h8 : sqrt 5 - 2 > 0 := by
          nlinarith
        positivity
    rw [h8, h9]
    norm_cast

  have h8 : (11 + 2 * sqrt 30 : ℝ) ^ ((3 : ℝ) / 2) = (sqrt 6 + sqrt 5) ^ 3 := by
    have h9 : (11 + 2 * sqrt 30 : ℝ) ^ ((3 : ℝ) / 2) = ((sqrt 6 + sqrt 5) ^ 2) ^ ((3 : ℝ) / 2) := by
      rw [h3]
    have h10 : ((sqrt 6 + sqrt 5 : ℝ) ^ 2) ^ ((3 : ℝ) / 2) = (sqrt 6 + sqrt 5 : ℝ) ^ (3 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul]
      norm_num
      all_goals
        positivity
    rw [h9, h10]
    norm_cast

  have h8' : (11 - 2 * sqrt 30 : ℝ) ^ ((3 : ℝ) / 2) = (sqrt 6 - sqrt 5) ^ 3 := by
    have h9 : (11 - 2 * sqrt 30 : ℝ) ^ ((3 : ℝ) / 2) = ((sqrt 6 - sqrt 5) ^ 2) ^ ((3 : ℝ) / 2) := by
      rw [h5]
    have h10 : ((sqrt 6 - sqrt 5 : ℝ) ^ 2) ^ ((3 : ℝ) / 2) = (sqrt 6 - sqrt 5 : ℝ) ^ (3 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul]
      norm_num
      all_goals
        have h7 : sqrt 6 > sqrt 5 := by
          apply Real.sqrt_lt_sqrt
          all_goals norm_num
          all_goals linarith
        have h8 : sqrt 6 - sqrt 5 > 0 := by
          nlinarith [Real.sqrt_nonneg 6, Real.sqrt_nonneg 5, h7]
        positivity
    rw [h9, h10]
    norm_cast

  rw [h7, h7', h8, h8']

  have h5_num : (sqrt 5 + 2 : ℝ) ^ 3 + (sqrt 5 - 2 : ℝ) ^ 3 = 34 * sqrt 5 := by
    ring_nf
    <;> nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), sq_nonneg (sqrt 5 ^ 2 - 4)]

  have h5_den : (sqrt 6 + sqrt 5 : ℝ) ^ 3 - (sqrt 6 - sqrt 5 : ℝ) ^ 3 = 46 * sqrt 5 := by
    have h3 : sqrt 6 ^ 2 = (6 : ℝ) := Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num)
    have h4 : sqrt 5 ^ 2 = (5 : ℝ) := Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)
    have h56 : sqrt 6 * sqrt 5 = sqrt 30 := by
      calc
        sqrt 6 * sqrt 5 = sqrt (6 * 5) := by rw [Real.sqrt_mul (by norm_num)]
        _ = sqrt 30 := by norm_num

    nlinarith [Real.sqrt_nonneg 6, Real.sqrt_nonneg 5, sq_nonneg (sqrt 6 ^ 2 - 6), sq_nonneg (sqrt 5 ^ 2 - 5), Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), Real.sqrt_nonneg 30, mul_nonneg (Real.sqrt_nonneg 6) (Real.sqrt_nonneg 5)]

  rw [h5_num, h5_den]

  have h5_pos : sqrt 5 > 0 := by
    positivity

  field_simp [h5_pos]
  <;> ring_nf <;> norm_num