import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_319652 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
  (h : a + 3 * b = 7) :
  13 / 14 + 4 * √3 / 14 ≤ 1 / (1 + a) + 4 / (2 + b) := by
  have ha2 : a = 7 - 3 * b := by linarith
  have hb2 : 7 - 3 * b > 0 := by
    rw [← ha2]
    linarith
  have h1 : 0 < 7 - 3 * b := by linarith [hb2]
  have h2 : 0 < 2 + b := by linarith [hb]
  have h3 : 1 / (1 + a) + 4 / (2 + b) = 1 / (8 - 3 * b) + 4 / (2 + b) := by
    have h4 : 1 + a = 8 - 3 * b := by
      rw [ha2]
      nlinarith
    rw [h4]
  rw [h3]
  have h4 : 0 < (8 - 3 * b) * (2 + b) := by
    apply mul_pos
    all_goals
    linarith
  have h5 : (1 / (8 - 3 * b) + 4 / (2 + b)) - (13 / 14 + 4 * √3 / 14) ≥ 0 := by
    have h7 : (1 / (8 - 3 * b) + 4 / (2 + b) ) - (13 / 14 + 4 * √3 / 14) =
        ( (28 + 14 * b + 448 - 168 * b - 208 - 26 * b + 39 * b ^ 2 - 64 * √3 - 8 * √3 * b + 12 * √3 * b ^ 2) ) / ((8 - 3 * b) * (2 + b) * 14) := by
      field_simp [(show 8 - 3 * b ≠ 0 by nlinarith), (show 2 + b ≠ 0 by nlinarith)]
      ring_nf
      <;> norm_num [Real.sqrt_mul_self]
      <;> ring
    rw [h7] at *
    have h8 : 28 + 14 * b + 448 - 168 * b - 208 - 26 * b + 39 * b ^ 2 - 64 * √3 - 8 * √3 * b + 12 * √3 * b ^ 2 ≥ 0 := by
      nlinarith [sq_nonneg (b - (102 - 28 * Real.sqrt 3) / 33), sq_nonneg (b * Real.sqrt 3 - (7 * Real.sqrt 3)/3), 
          sq_nonneg (b - (Real.sqrt 3)/3 * 7), sq_nonneg (b - (7 * Real.sqrt 3)/3), 
          sq_nonneg (b^2 * Real.sqrt 3 - (4 * Real.sqrt 3)/3 * b + 1/3), 
          Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), 
          sq_nonneg (b - 1), sq_nonneg (b - (7/3)), sq_nonneg (b - (102 - 28 * Real.sqrt 3) / 33), 
          mul_pos hb (show 0 < 7/3 - b by nlinarith [show 7 - 3 * b > 0 by linarith]) 
        ]
    have h9 : ( (28 + 14 * b + 448 - 168 * b - 208 - 26 * b + 39 * b ^ 2 - 64 * √3 - 8 * √3 * b + 12 * √3 * b ^ 2) ) ≥ 0 := by
      linarith
    have h10 : ( (28 + 14 * b + 448 - 168 * b - 208 - 26 * b + 39 * b ^ 2 - 64 * √3 - 8 * √3 * b + 12 * √3 * b ^ 2) ) / ((8 - 3 * b) * (2 + b) * 14) ≥ 0 := by
      apply div_nonneg
      linarith
      positivity
    linarith
  linarith