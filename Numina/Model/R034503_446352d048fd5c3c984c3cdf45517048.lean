import Mathlib

open Real Set
open scoped BigOperators
theorem algebra_12235 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
  (h : a + 3 * b = 7) :
  1 / (1 + a) + 4 / (2 + b) ≥ (13 + 4 * sqrt 3) / 14 := by
  have ha1 : a = 7 - 3 * b := by
    linarith
  rw [ha1]
  have hb1 : 0 < b := hb
  have hb2 : b < 7 / 3 := by
    nlinarith [show 0 < (7 - 3 * b : ℝ) from by nlinarith [ha, h]]
  have h1 : 0 < (1 + (7 - 3 * b) : ℝ) := by
    nlinarith [show (0 < (7 - 3 * b : ℝ)) from by nlinarith [ha, h], ha]

  have h2 : 0 < (2 + b : ℝ) := by
    linarith
  have h3 : 1 / (1 + (7 - 3 * b) : ℝ) + 4 / (2 + b : ℝ) - (13 + 4 * sqrt 3) / 14 ≥ 0 := by
    have h4 : (1 + (7 - 3 * b) : ℝ) > 0 := by
      nlinarith [show (0 < (7 - 3 * b : ℝ)) from by nlinarith [ha, h], ha]
    have h5 : (2 + b : ℝ) > 0 := by
      linarith
    have h6 : (14 : ℝ) > 0 := by
      norm_num
    have h7 : (1 / (1 + (7 - 3 * b) : ℝ) + 4 / (2 + b : ℝ) - (13 + 4 * sqrt 3) / 14) ≥ 0 := by
      have h8 : (1 / (1 + (7 - 3 * b) : ℝ) + 4 / (2 + b : ℝ) - (13 + 4 * sqrt 3) / 14) =
          (14 * (2 + b) + 14 * 4 * (1 + (7 - 3 * b)) - (13 + 4 * sqrt 3) * (1 + (7 - 3 * b)) * (2 + b)) / (14 * (1 + (7 - 3 * b)) * (2 + b)) := by
        field_simp
        ring
      rw [h8]
      have h9 : (14 * (1 + (7 - 3 * b)) * (2 + b) ) > 0 := by
        positivity
      have h10 : (14 * (2 + b) + 14 * 4 * (1 + (7 - 3 * b)) - (13 + 4 * sqrt 3) * (1 + (7 - 3 * b)) * (2 + b) ) ≥ 0 := by
        nlinarith [Real.sqrt_pos.mpr (by norm_num : (3 : ℝ) > 0), sq_nonneg (sqrt 3), Real.sqrt_nonneg 3, Real.mul_self_sqrt (show 0 ≤ (3 : ℝ) by norm_num), sq_nonneg ((b) - (102 - 28 * sqrt 3)/33), mul_pos (show 0 < (3 : ℝ) by norm_num) (Real.sqrt_pos.mpr (by norm_num : (3 : ℝ) > 0))]
      apply div_nonneg
      linarith
      all_goals linarith
    linarith
  linarith