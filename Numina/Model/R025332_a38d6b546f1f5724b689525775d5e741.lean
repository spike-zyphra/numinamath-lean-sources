import Mathlib

open Real

theorem algebra_187632 : sqrt (6 + sqrt 11) - sqrt (6 - sqrt 11) = sqrt 2 := by
  have h1 : sqrt (6 + sqrt 11) ≥ 0 := Real.sqrt_nonneg (6 + sqrt 11)
  have h2 : sqrt (6 - sqrt 11) ≥ 0 := Real.sqrt_nonneg (6 - sqrt 11)
  have h3 : (sqrt (6 + sqrt 11) - sqrt (6 - sqrt 11)) ^ 2 = 2 := by
    have h4 : (sqrt (6 + sqrt 11)) ^ 2 = 6 + sqrt 11 := by
      rw [Real.sq_sqrt]
      positivity
    have h5 : (sqrt (6 - sqrt 11)) ^ 2 = 6 - sqrt 11 := by
      rw [Real.sq_sqrt]
      have h6 : sqrt 11 ≥ 0 := Real.sqrt_nonneg 11
      have h7 : sqrt 11 ≤ 6 := by
        nlinarith [Real.sqrt_nonneg 11, Real.sq_sqrt (show (0 : ℝ) ≤ 11 by norm_num)]
      nlinarith [Real.sqrt_nonneg 11, Real.sq_sqrt (show (0 : ℝ) ≤ 11 by norm_num)]
    have h8 : sqrt (6 + sqrt 11) * sqrt (6 - sqrt 11) = (5 : ℝ) := by
      have h9 : sqrt (6 + sqrt 11) * sqrt (6 - sqrt 11) = Real.sqrt ((6 + sqrt 11) * (6 - sqrt 11)) := by
        rw [← Real.sqrt_mul (by
          have h14 : sqrt 11 ≥ 0 := Real.sqrt_nonneg 11
          have h15 : sqrt 11 ≤ (6 : ℝ) := by
            nlinarith [Real.sqrt_nonneg 11, Real.sq_sqrt (show (0 : ℝ) ≤ 11 by norm_num)]
          nlinarith [Real.sqrt_nonneg 11]
        )]
      rw [h9]
      have h10 : ((6 + sqrt 11) * (6 - sqrt 11)) = (25 : ℝ) := by
        nlinarith [Real.sqrt_nonneg 11, Real.sq_sqrt (show (0 : ℝ) ≤ (11 : ℝ) by norm_num)]
      rw [h10]
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    calc
      (sqrt (6 + sqrt 11) - sqrt (6 - sqrt 11)) ^ 2
        = (sqrt (6 + sqrt 11)) ^ 2 + (sqrt (6 - sqrt 11)) ^ 2 - 2 * (sqrt (6 + sqrt 11) * sqrt (6 - sqrt 11)) := by ring
      _ = (6 + sqrt 11) + (6 - sqrt 11) - 2 * (5 : ℝ) := by rw [h4, h5, h8]
      _ = (2 : ℝ) := by
        nlinarith [Real.sqrt_nonneg 11]
  have h8 : sqrt (6 + sqrt 11) - sqrt (6 - sqrt 11) ≥ 0 := by
    have h7 : sqrt (6 + sqrt 11) ≥ sqrt (6 - sqrt 11) := by
      apply Real.sqrt_le_sqrt
      have h8 : sqrt 11 ≥ 0 := Real.sqrt_nonneg 11
      have h9 : sqrt 11 ≤ 6 := by
        nlinarith [Real.sqrt_nonneg 11, Real.sq_sqrt (show (0 : ℝ) ≤ 11 by norm_num)]
      nlinarith [Real.sqrt_nonneg 11, Real.sq_sqrt (show (0 : ℝ) ≤ (11 : ℝ) by norm_num)]
    linarith [h7]
  have h9 : Real.sqrt ((sqrt (6 + sqrt 11) - sqrt (6 - sqrt 11)) ^ 2) = sqrt 2 := by
    have h10 : (sqrt (6 + sqrt 11) - sqrt (6 - sqrt 11)) ^ 2 = (2 : ℝ) := h3
    rw [h10]
    all_goals norm_num
  have h11 : Real.sqrt ((sqrt (6 + sqrt 11) - sqrt (6 - sqrt 11)) ^ 2) = (sqrt (6 + sqrt 11) - sqrt (6 - sqrt 11) : ℝ) := by
    rw [Real.sqrt_sq (show 0 ≤ (sqrt (6 + sqrt 11) - sqrt (6 - sqrt 11)) by linarith [h8]) ]
  linarith [h9, h11]