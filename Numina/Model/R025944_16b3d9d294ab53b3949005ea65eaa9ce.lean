import Mathlib

open Real

theorem algebra_273637 : (sqrt (sqrt 5 + 2) + sqrt (sqrt 5 - 2)) / sqrt (sqrt 5 + 1) - sqrt (3 - 2 * sqrt 2) = 1 := by

  have h1 : sqrt (3 - 2 * sqrt 2) = sqrt 2 - 1 := by
    have h2 : (sqrt 2 - 1 : ℝ) ^ 2 = 3 - 2 * sqrt 2 := by
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    have h3 : sqrt (3 - 2 * sqrt 2) = sqrt ((sqrt 2 - 1 : ℝ) ^ 2) := by
      rw [h2]
    rw [h3]
    have h4 : sqrt ((sqrt 2 - 1 : ℝ) ^ 2) = sqrt 2 - 1 := by
      apply Real.sqrt_sq
      have h5 : 1 < sqrt 2 := by
        rw [Real.lt_sqrt] <;> norm_num
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    exact h4

  have h6 : (sqrt (sqrt 5 + 2) + sqrt (sqrt 5 - 2)) ^ 2 = 2 * sqrt 5 + 2 := by
    have h51 : (sqrt (sqrt 5 + 2) : ℝ) ^ 2 = sqrt 5 + 2 := by
      exact Real.sq_sqrt (by
        have h5 : sqrt 5 ≥ 0 := Real.sqrt_nonneg 5
        nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]
      )
    have h52 : (sqrt (sqrt 5 - 2) : ℝ) ^ 2 = sqrt 5 - 2 := by
      exact Real.sq_sqrt (by
        have h5 : sqrt 5 ≥ 2 := by
          nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), sq_nonneg (sqrt 5 - 2)]
        nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]
      )
    have h53 : sqrt (sqrt 5 + 2) * sqrt (sqrt 5 - 2) = 1 := by
      have h54 : sqrt (sqrt 5 + 2) * sqrt (sqrt 5 - 2) = Real.sqrt ((sqrt 5 + 2) * (sqrt 5 - 2)) := by
        rw [← Real.sqrt_mul (by
          have h5 : sqrt 5 + 2 ≥ 0 := by
            nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
          linarith
        )]
      rw [h54]
      have h55 : (sqrt 5 + 2) * (sqrt 5 - 2) = 1 := by
        nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
      rw [h55]
      all_goals norm_num
    nlinarith [h51, h52, h53, Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]

  have h7 : ((sqrt (sqrt 5 + 2) + sqrt (sqrt 5 - 2)) / sqrt (sqrt 5 + 1)) ^ 2 = 2 := by
    have h51 : sqrt (sqrt 5 + 1) ≥ 0 := by positivity
    have h52 : (sqrt (sqrt 5 + 1)) ^ 2 = sqrt 5 + 1 := by
      exact Real.sq_sqrt (by
        have h5 : sqrt 5 ≥ 0 := Real.sqrt_nonneg 5
        nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
      )
    calc
      ((sqrt (sqrt 5 + 2) + sqrt (sqrt 5 - 2)) / sqrt (sqrt 5 + 1)) ^ 2
          = ((sqrt (sqrt 5 + 2) + sqrt (sqrt 5 - 2)) ^ 2) / ((sqrt (sqrt 5 + 1)) ^ 2) := by
            field_simp
      _ = (2 * sqrt 5 + 2) / ((sqrt (sqrt 5 + 1)) ^ 2) := by
        rw [h6]
      _ = (2 * sqrt 5 + 2) / (sqrt 5 + 1) := by
        rw [h52]
      _ = 2 := by
        field_simp [(show sqrt 5 + 1 ≠ 0 by positivity)]
        <;> nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]

  have h8 : (sqrt (sqrt 5 + 2) + sqrt (sqrt 5 - 2)) / sqrt (sqrt 5 + 1) = Real.sqrt 2 := by
    have h11 : Real.sqrt (( (sqrt (sqrt 5 + 2) + sqrt (sqrt 5 - 2)) / sqrt (sqrt 5 + 1) ) ^ 2) = Real.sqrt 2 := by
      rw [h7]
      <;> norm_num
    have h12 : 0 ≤ (sqrt (sqrt 5 + 2) + sqrt (sqrt 5 - 2)) / sqrt (sqrt 5 + 1) := by
      apply div_nonneg
      · -- Show that sqrt (sqrt 5 + 2) + sqrt (sqrt 5 - 2) ≥ 0
        linarith [show sqrt (sqrt 5 + 2) ≥ 0 by positivity, show sqrt (sqrt 5 - 2) ≥ 0 by positivity]
      · -- Show that sqrt (sqrt 5 + 1) ≥ 0
        positivity
    have h13 : Real.sqrt ( ((sqrt (sqrt 5 + 2) + sqrt (sqrt 5 - 2)) / sqrt (sqrt 5 + 1)) ^ 2 ) = (sqrt (sqrt 5 + 2) + sqrt (sqrt 5 - 2)) / sqrt (sqrt 5 + 1) := by
      rw [Real.sqrt_sq (show 0 ≤ (sqrt (sqrt 5 + 2) + sqrt (sqrt 5 - 2)) / sqrt (sqrt 5 + 1) by linarith [h12] ) ]
    rw [h13] at h11
    linarith

  rw [h1]
  rw [h8]
  nlinarith [Real.sqrt_nonneg 2, Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), Real.sqrt_nonneg (sqrt 5 + 2), Real.sqrt_nonneg (sqrt 5 - 2), Real.sqrt_nonneg (sqrt 5 + 1), Real.sqrt_nonneg (3 - 2 * sqrt 2)]