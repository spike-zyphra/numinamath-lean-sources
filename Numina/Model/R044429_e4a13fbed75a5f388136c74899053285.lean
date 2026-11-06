import Mathlib

open Real

theorem algebra_302082 : ⌊1 / sqrt (16 - 6 * sqrt 7)⌋ = 2 := by
  have h1 : sqrt (16 - 6 * sqrt 7) = 3 - Real.sqrt 7 := by
    have h2 : (3 - Real.sqrt 7 : ℝ) ^ 2 = 16 - 6 * Real.sqrt 7 := by
      nlinarith [Real.sqrt_nonneg 7, Real.sq_sqrt (show (0 : ℝ) ≤ 7 by norm_num)]
    have h3 : 3 - Real.sqrt 7 ≥ 0 := by
      nlinarith [Real.sqrt_nonneg 7, Real.sq_sqrt (show (0 : ℝ) ≤ 7 by norm_num), sq_nonneg (3 - Real.sqrt 7)]
    rw [← h2]
    field_simp [Real.sqrt_sq h3]

  have h4 : 1 / sqrt (16 - 6 * sqrt 7) = (3 + Real.sqrt 7) / 2 := by
    rw [h1]
    have h5 : (3 - Real.sqrt 7 : ℝ) ≠ 0 := by
      nlinarith [Real.sqrt_nonneg 7, Real.sq_sqrt (show (0 : ℝ) ≤ 7 by norm_num)]
    field_simp [h5]
    <;> nlinarith [Real.sqrt_nonneg 7, Real.sq_sqrt (show (0 : ℝ) ≤ 7 by norm_num)]

  rw [h4]
  have h5 : 2 ≤ (3 + Real.sqrt 7) / 2 := by
    nlinarith [Real.sqrt_nonneg 7, Real.sq_sqrt (show (0 : ℝ) ≤ 7 by norm_num)]
  have h6 : (3 + Real.sqrt 7) / 2 < 3 := by
    nlinarith [Real.sqrt_nonneg 7, Real.sq_sqrt (show (0 : ℝ) ≤ 7 by norm_num)]
  rw [Int.floor_eq_iff]
  constructor <;> (try norm_num) <;> try linarith