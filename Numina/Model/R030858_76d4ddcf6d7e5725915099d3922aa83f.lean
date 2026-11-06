import Mathlib

open Real

theorem algebra_1523 {a : ℝ}
    (ha : a = (1 / 2) * sqrt (sqrt 2 + (1 / 8)) - (1 / 8) * sqrt 2) :
    a^2 + sqrt ((a^4) + a + 1) = sqrt 2 := by
  have ha1 : a = (1 / 2) * sqrt (sqrt 2 + 1 / 8) - (1 / 8) * sqrt 2 := by
    ring_nf at ha ⊢
    linarith
  have h2 : 0 ≤ (a ^ 4 + a + 1) := by
    rw [ha1]
    nlinarith [sq_nonneg (sqrt (sqrt 2 + 1 / 8) ^ 2 - 2), sq_nonneg (sqrt 2), sq_nonneg ((1 / 2) * sqrt (sqrt 2 + (1 / 8)) - (1 / 8) * sqrt 2), sq_nonneg ((1 / 2) * sqrt (sqrt 2 + (1 / 8)) ^ 2 - (1 / 4) * sqrt 2), sq_nonneg ((1 / 8) * sqrt 2 ^ 2 - (1 / 16) * 2), Real.sqrt_nonneg (2 : ℝ), Real.sqrt_nonneg (sqrt 2 + 1 / 8), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (sqrt 2 + (1 / 8) : ℝ) by positivity)]
  have h4 : sqrt ((a^4) + a + 1) = (sqrt 2 - a ^ 2) := by
    have h5 : sqrt ((a ^ 4 + a + 1 : ℝ)) ≥ 0 := by positivity
    have h6 : (sqrt 2 - a ^ 2) ≥ 0 := by
      rw [ha1]
      nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sqrt_nonneg (sqrt 2 + (1 / 8) : ℝ), 
                sq_nonneg (sqrt (sqrt 2 + (1 / 8) : ℝ) ^ 2 - 2 : ℝ), sq_nonneg (sqrt 2 ^ 2 - 2 : ℝ), 
                Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num : (0 : ℝ) ≤ (2 : ℝ)), 
                Real.sq_sqrt (show (0 : ℝ) ≤ (sqrt 2 + (1 / 8) : ℝ) by positivity)]
    have h7 : (sqrt ((a ^ 4 + a + 1 : ℝ))) ^ 2 = (sqrt 2 - a ^ 2) ^ 2 := by
      have h8 : (sqrt ((a ^ 4 + a + 1 : ℝ))) ^ 2 = ((a ^ 4 + a + 1) : ℝ) := by
        rw [Real.sq_sqrt]
        linarith
      have h9 : ((sqrt 2 - a ^ 2) : ℝ) ^ 2 = (a ^ 4 + a + 1 : ℝ) := by
        rw [ha1]
        nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sqrt_nonneg (sqrt 2 + 1 / 8 : ℝ), 
                  sq_nonneg (sqrt (sqrt 2 + (1 / 8) : ℝ) ^ 2 - 2 : ℝ), sq_nonneg (sqrt 2 ^ 2 - 2 : ℝ), 
                  Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num : (0 : ℝ) ≤ (2 : ℝ)), 
                  Real.sq_sqrt (show (0 : ℝ) ≤ (sqrt 2 + (1 / 8) : ℝ) by positivity)]
      nlinarith
    have h8 : (sqrt ((a ^ 4 + a + 1) : ℝ) ) = (sqrt 2 - a ^ 2 : ℝ) := by
      nlinarith [Real.sqrt_nonneg (a ^ 4 + a + 1 : ℝ), Real.sqrt_nonneg (2 : ℝ), h6]
    linarith
  have h5 : a^2 + sqrt ((a^4) + a + 1) = sqrt 2 := by
    nlinarith [Real.sqrt_nonneg (a ^ 4 + a + 1 : ℝ), Real.sqrt_nonneg (2 : ℝ), sq_nonneg (a ^ 2 : ℝ), h4]
  linarith
  all_goals nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sqrt_nonneg (sqrt 2 + 1 / 8)]