import Mathlib

open Real

theorem algebra_183493 : (sqrt (7 + 2 * sqrt 10) + sqrt (7 - 2 * sqrt 10))^2 = 20 := by

  have h1 : sqrt (7 + 2 * sqrt 10) = sqrt 5 + sqrt 2 := by
    have h2 : (sqrt 5 + sqrt 2) ^ 2 = 7 + 2 * sqrt 10 := by
      have h5 : (sqrt 5) ^ 2 = 5 := by
        exact sq_sqrt (by norm_num)
      have h2' : (sqrt 2) ^ 2 = 2 := by
        exact sq_sqrt (by norm_num)
      have h52 : sqrt 5 * sqrt 2 = sqrt 10 := by
        have h10 : sqrt 10 = sqrt (5 * 2) := by
          norm_num
        rw [h10]
        rw [Real.sqrt_mul (by norm_num)]
        all_goals norm_num
      nlinarith [Real.sqrt_nonneg 5, Real.sqrt_nonneg 2, h5, h2', h52]
      all_goals nlinarith [Real.sqrt_nonneg 10, Real.sqrt_nonneg 5, Real.sqrt_nonneg 2]
    rw [← h2]
    rw [Real.sqrt_sq (by
      nlinarith [Real.sqrt_nonneg 5, Real.sqrt_nonneg 2]
    )]

  have h3 : sqrt (7 - 2 * sqrt 10) = sqrt 5 - sqrt 2 := by
    have h4 : (sqrt 5 - sqrt 2) ^ 2 = 7 - 2 * sqrt 10 := by
      have h5 : (sqrt 5) ^ 2 = 5 := by
        exact sq_sqrt (by norm_num)
      have h2' : (sqrt 2) ^ 2 = 2 := by
        exact sq_sqrt (by norm_num)
      have h52 : sqrt 5 * sqrt 2 = sqrt 10 := by
        have h10 : sqrt 10 = sqrt (5 * 2) := by
          norm_num
        rw [h10]
        rw [Real.sqrt_mul (by norm_num)]
        all_goals norm_num
      nlinarith [Real.sqrt_nonneg 5, Real.sqrt_nonneg 2, h5, h2', h52]
      all_goals nlinarith [Real.sqrt_nonneg 10, Real.sqrt_nonneg 5, Real.sqrt_nonneg 2]
    have h5 : sqrt 5 ≥ sqrt 2 := by
      apply Real.sqrt_le_sqrt
      all_goals norm_num
    have h6 : sqrt 5 - sqrt 2 ≥ 0 := by nlinarith [Real.sqrt_nonneg 5, Real.sqrt_nonneg 2, h5]
    rw [← h4]
    rw [Real.sqrt_sq (by
      linarith [h6]
    )]

  have h7 : (sqrt 5 + sqrt 2) + (sqrt 5 - sqrt 2) = 2 * sqrt 5 := by
    ring

  rw [h1, h3]

  have h8 : (2 * sqrt 5) ^ 2 = 20 := by
    calc
      (2 * sqrt 5) ^ 2 = 4 * (sqrt 5) ^ 2 := by ring
      _ = 4 * 5 := by rw [Real.sq_sqrt (show (5 : ℝ) ≥ 0 by norm_num)]
      _ = 20 := by norm_num

  rw [h7]
  linarith [h8]