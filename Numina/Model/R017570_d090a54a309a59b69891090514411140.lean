import Mathlib

open Real

theorem inequalities_320387 (a b : ℝ) (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) :
    2 * sqrt 2 ≤ sqrt (a ^ 2 + b ^ 2) + sqrt ((1 - a) ^ 2 + b ^ 2) +
    sqrt (a ^ 2 + (1 - b) ^ 2) + sqrt ((1 - a) ^ 2 + (1 - b) ^ 2) := by

  have h1 : 0 < a := ha.1
  have h2 : a < 1 := ha.2
  have h3 : 0 < b := hb.1
  have h4 : b < 1 := hb.2

  have h5 : sqrt (a ^ 2 + b ^ 2) ≥ Real.sqrt 2 / 2 * (a + b) := by
    have h6 : (a ^ 2 + b ^ 2 : ℝ) ≥ ( (Real.sqrt 2 / 2 * (a + b)) ^ 2 ) := by
      nlinarith [ sq_nonneg (a - b), Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num) ]
    have h7 : Real.sqrt (a ^ 2 + b ^ 2) ≥ Real.sqrt ( (Real.sqrt 2 / 2 * (a + b)) ^ 2 ) := by
      apply Real.sqrt_le_sqrt
      linarith
    have h8 : Real.sqrt ( (Real.sqrt 2 / 2 * (a + b)) ^ 2 ) = Real.sqrt 2 / 2 * (a + b) := by
      rw [ Real.sqrt_sq (by nlinarith [ Real.sqrt_nonneg 2, h1, h2, h3, h4 ] ) ]
    nlinarith

  have h6 : sqrt ((1 - a) ^ 2 + b ^ 2) ≥ Real.sqrt 2 / 2 * ((1 - a) + b) := by
    have h7 : ( (1 - a) ^ 2 + b ^ 2 : ℝ) ≥ ( (Real.sqrt 2 / 2 * ((1 - a) + b)) ^ 2 ) := by
      nlinarith [ sq_nonneg ((1 - a) - b), Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num) ]
    have h8 : Real.sqrt ( (1 - a) ^ 2 + b ^ 2) ≥ Real.sqrt ( (Real.sqrt 2 / 2 * ((1 - a) + b)) ^ 2 ) := by
      apply Real.sqrt_le_sqrt
      linarith
    have h9 : Real.sqrt ( (Real.sqrt 2 / 2 * ((1 - a) + b)) ^ 2 ) = Real.sqrt 2 / 2 * ((1 - a) + b) := by
      rw [ Real.sqrt_sq (by nlinarith [ Real.sqrt_nonneg 2, h1, h2, h3, h4 ] ) ]
    nlinarith

  have h7 : sqrt (a ^ 2 + (1 - b) ^ 2) ≥ Real.sqrt 2 / 2 * (a + (1 - b)) := by
    have h8 : (a ^ 2 + (1 - b) ^ 2 : ℝ) ≥ ( (Real.sqrt 2 / 2 * (a + (1 - b))) ^ 2 ) := by
      nlinarith [ sq_nonneg (a - (1 - b)), Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num) ]
    have h9 : Real.sqrt (a ^ 2 + (1 - b) ^ 2) ≥ Real.sqrt ( (Real.sqrt 2 / 2 * (a + (1 - b))) ^ 2 ) := by
      apply Real.sqrt_le_sqrt
      linarith
    have h10 : Real.sqrt ( (Real.sqrt 2 / 2 * (a + (1 - b))) ^ 2 ) = Real.sqrt 2 / 2 * (a + (1 - b)) := by
      rw [ Real.sqrt_sq (by nlinarith [ Real.sqrt_nonneg 2, h1, h2, h3, h4 ] ) ]
    nlinarith

  have h8 : sqrt ((1 - a) ^ 2 + (1 - b) ^ 2) ≥ Real.sqrt 2 / 2 * ((1 - a) + (1 - b)) := by
    have h9 : ( (1 - a) ^ 2 + (1 - b) ^ 2 : ℝ) ≥ ( (Real.sqrt 2 / 2 * ((1 - a) + (1 - b))) ^ 2 ) := by
      nlinarith [ sq_nonneg ((1 - a) - (1 - b)), Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num) ]
    have h10 : Real.sqrt ( (1 - a) ^ 2 + (1 - b) ^ 2) ≥ Real.sqrt ( (Real.sqrt 2 / 2 * ((1 - a) + (1 - b))) ^ 2 ) := by
      apply Real.sqrt_le_sqrt
      linarith
    have h11 : Real.sqrt ( (Real.sqrt 2 / 2 * ((1 - a) + (1 - b))) ^ 2 ) = Real.sqrt 2 / 2 * ((1 - a) + (1 - b)) := by
      rw [ Real.sqrt_sq (by nlinarith [ Real.sqrt_nonneg 2, h1, h2, h3, h4 ] ) ]
    nlinarith

  have h9 : sqrt (a ^ 2 + b ^ 2) + sqrt ((1 - a) ^ 2 + b ^ 2) + sqrt (a ^ 2 + (1 - b) ^ 2) + sqrt ((1 - a) ^ 2 + (1 - b) ^ 2) ≥ 2 * sqrt 2 := by
    nlinarith [ h5, h6, h7, h8, Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num) ]
  linarith