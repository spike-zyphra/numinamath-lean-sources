import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_151684 (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
  (h : x + 2 * y = 1) :
  (x + 1 / x) * (y + 1 / (4 * y)) ≥ 25 / 8 := by

  have h3 : 0 < 4 * y := by nlinarith
  have h4 : 0 < x * y := mul_pos hx hy
  have h5 : 0 < 4 * x * y := by
    nlinarith

  have h7 : (x + 1 / x) * (y + 1 / (4 * y)) - 25 / 8 ≥ 0 := by
    have h8 : x * (4 * y) > 0 := mul_pos hx (by linarith)
    have h9 : (x + 1 / x) * (y + 1 / (4 * y)) - 25 / 8 =
        (8 * x ^ 2 * y ^ 2 + 2 * x ^ 2 + 8 * y ^ 2 + 2 - 25 * (x * y)) / (8 * x * y) := by
      field_simp
      ring
    rw [h9] at *
    have h3 : 0 < 8 * x * y := by
      nlinarith [h4]
    have h4 : 8 * x ^ 2 * y ^ 2 + 2 * x ^ 2 + 8 * y ^ 2 + 2 - 25 * (x * y) ≥ 0 := by
      nlinarith [sq_nonneg (x - 1 / 2), sq_nonneg (y - 1 / 4), 
                sq_nonneg (x * y - 1 / 8), sq_nonneg (x - 2 * y), 
                mul_pos hx hy, 
                mul_pos hx (show 0 < 1 - x by nlinarith), 
                mul_pos hy (show 0 < 1 - x by nlinarith)
              ]
    apply div_nonneg
    linarith
    all_goals
      nlinarith
  linarith