import Mathlib

open Real Set
open scoped BigOperators
/-Given positive numbers a, b satisfy a + 3b = 7, then the minimum value of 1/(1+a) + 4/(2+b) is ?-/
theorem algebra_12235 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
  (h : a + 3 * b = 7) :
  1 / (1 + a) + 4 / (2 + b) ≥ (13 + 4 * sqrt 3) / 14 := by
  -- replace a by expression of b
    have h1 : a = 7 - 3 * b := by linarith
    rw [h1]
    have h2 : 7 - 3 * b > 0 := by nlinarith
    have h3 : 2 + b > 0 := by nlinarith
    have h4 : 8 - 3 * b > 0 := by nlinarith
    -- prove one variable inequality 
    have h5 : 1 / (1 + (7 - 3 * b)) + 4 / (2 + b) ≥ (13 + 4 * sqrt 3) / 14 := by
      have h6 : (13 + 4 * sqrt 3) / 14 > 0 := by
        positivity
      have h7 : 1 / (1 + (7 - 3 * b)) + 4 / (2 + b) - (13 + 4 * sqrt 3) / 14 ≥ 0 := by
        have h7 : (sqrt 3) ^ 2 = 3 := Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)
        have h9 : 8 - 3 * b > 0 := h4
        have h10 : 2 + b > 0 := h3
        -- write the left side as a single fraction --
        have h11 : (1 / (1 + (7 - 3 * b)) + 4 / (2 + b) - (13 + 4 * sqrt 3) / 14) = 
            (476 - 154 * b - (13 + 4 * sqrt 3) * (8 - 3 * b) * (2 + b)) / (14 * (8 - 3 * b) * (2 + b)) := by
            field_simp
            nlinarith [h6, h9, h10, sq_nonneg (sqrt 3), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), mul_pos ha hb]
        rw [h11]
        -- it suffices to show that the numerator is nonnegative --
        have h12 : 476 - 154 * b - (13 + 4 * sqrt 3) * (8 - 3 * b) * (2 + b) ≥ 0 := by -- using completing the square
            nlinarith [sq_nonneg (b - (102 - 28 * sqrt 3) / 33), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num),
              sq_nonneg (sqrt 3 - 2), sq_nonneg (sqrt 3 - 1)]
        apply div_nonneg
        · linarith
        · nlinarith [h9, h10]
      linarith
    linarith [h5]