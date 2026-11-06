import Mathlib

open Real

theorem algebra_313734 : sqrt 2 * (sqrt 6 - sqrt 3 - sqrt 2 + 1) / (sqrt (3 - 2 * sqrt 2) * sqrt (2 - sqrt 3)) = 2 := by

  have h1 : sqrt (3 - 2 * sqrt 2) = sqrt 2 - 1 := by
    have h2 : (sqrt 2 - 1 : ℝ) ^ 2 = (3 - 2 * sqrt 2 : ℝ) := by
      nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    have h3 : sqrt (3 - 2 * sqrt 2 : ℝ) = sqrt 2 - 1 := by
      have h4 : (sqrt 2 - 1 : ℝ) ≥ 0 := by
        have h5 : sqrt 2 ≥ 1 := by
          have h6 : sqrt 2 ≥ sqrt 1 := Real.sqrt_le_sqrt (by norm_num)
          have h7 : sqrt 1 = (1 : ℝ) := Real.sqrt_one
          linarith [h6, h7]
        linarith
      rw [← h2]
      field_simp [Real.sqrt_nonneg (2 : ℝ), Real.sqrt_nonneg (3 - 2 * sqrt 2 : ℝ), h4]
    exact h3

  have h4 : sqrt (2 - sqrt 3) = (sqrt 3 - 1) / sqrt 2 := by
    have h5 : ((sqrt 3 - 1) / sqrt 2 : ℝ) ^ 2 = (2 - sqrt 3 : ℝ) := by
      have h6 : sqrt 2 > 0 := by
        positivity
      field_simp
      nlinarith [Real.sqrt_nonneg (3 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    have h7 : ((sqrt 3 - 1) / sqrt 2 : ℝ) ≥ 0 := by
      have h8 : sqrt 3 ≥ 1 := by
        have h9 : sqrt 3 ≥ sqrt 1 := Real.sqrt_le_sqrt (by norm_num)
        have h10 : sqrt 1 = (1 : ℝ) := Real.sqrt_one
        linarith [h9, h10]
      have h11 : sqrt 3 - 1 ≥ 0 := by
        nlinarith
      have h12 : sqrt 2 > 0 := by
        positivity
      apply div_nonneg
      · linarith
      · linarith
    have h8 : sqrt (2 - sqrt 3 : ℝ) = (sqrt 3 - 1) / sqrt 2 := by
      rw [← h5]
      field_simp [Real.sqrt_nonneg (2 - sqrt 3 : ℝ), h7]
    exact h8

  rw [h1, h4]

  have h10 : sqrt 2 > 0 := by positivity
  have h11 : sqrt 3 > 0 := by positivity

  have h12 : sqrt 2 * (sqrt 6 - sqrt 3 - sqrt 2 + 1) / ((sqrt 2 - 1) * ((sqrt 3 - 1) / sqrt 2)) = 2 := by
    have h13 : sqrt 2 * (sqrt 6 - sqrt 3 - sqrt 2 + 1) / ((sqrt 2 - 1) * ((sqrt 3 - 1) / sqrt 2)) =
      (sqrt 2 * (sqrt 6 - sqrt 3 - sqrt 2 + 1) * sqrt 2) / ((sqrt 2 - 1) * (sqrt 3 - 1)) := by
      field_simp [h10]
      all_goals
        ring
    rw [h13]

    have h14 : sqrt 2 * (sqrt 6 - sqrt 3 - sqrt 2 + 1) * sqrt 2 = 2 * (sqrt 6 - sqrt 3 - sqrt 2 + 1) := by
      have h15 : sqrt 2 * (sqrt 6 - sqrt 3 - sqrt 2 + 1) * sqrt 2 = (sqrt 2 * sqrt 2) * (sqrt 6 - sqrt 3 - sqrt 2 + 1) := by
        ring
      rw [h15]
      have h16 : sqrt 2 * sqrt 2 = 2 := by
        calc
          sqrt 2 * sqrt 2 = (sqrt 2) ^ 2 := by ring
          _ = (2 : ℝ) := by rw [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
      rw [h16]

    rw [h14]

    have h17 : (sqrt 2 - 1) * (sqrt 3 - 1) = sqrt 6 - sqrt 2 - sqrt 3 + 1 := by
      have h18 : sqrt 6 = sqrt 2 * sqrt 3 := by
        have h19 : sqrt 6 = sqrt (2 * 3) := by
          norm_num
        rw [h19]
        rw [Real.sqrt_mul (by norm_num)]
      nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sqrt_nonneg (3 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num)]

    rw [h17]

    have h18 : sqrt 6 - sqrt 3 - sqrt 2 + 1 = sqrt 6 - sqrt 2 - sqrt 3 + 1 := by ring

    rw [h18]

    have h20 : sqrt 6 - sqrt 2 - sqrt 3 + 1 ≠ 0 := by
      nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sqrt_nonneg (3 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num), mul_nonneg (Real.sqrt_nonneg (2 : ℝ)) (Real.sqrt_nonneg (3 : ℝ)), sq_nonneg (sqrt 2 - 1 : ℝ), sq_nonneg (sqrt 3 - 1 : ℝ)]

    field_simp [h20]
    all_goals
      nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sqrt_nonneg (3 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num)]

  exact h12